/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules
import Atlas.LieGroups.code.HarishChandraIsomorphism
import Atlas.LieGroups.code.HilbertNoether
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def HasWeightDecomposition (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] : Prop :=
  ∀ m : M, ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)) (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ),
    m = ∑ μ ∈ S, (v μ : M)

structure IsCategoryO (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  finitely_generated : ∃ (S : Finset M), LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤
  weight_decomp : HasWeightDecomposition Δ M
  weight_bound : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
    ∀ μ ∈ weights Δ M, ∃ wt ∈ bds, rd.IsInQPlus (wt - μ)

theorem PositiveRootData.IsInQPlus_zero
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) :
    rd.IsInQPlus 0 :=
  ⟨fun _ => 0, by simp⟩

theorem PositiveRootData.IsInQPlus_trans
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wt0 μ ν : Δ.𝔥 →ₗ[R] R)
    (h1 : rd.IsInQPlus (wt0 - μ))
    (h2 : rd.IsInQPlus (μ - ν)) :
    rd.IsInQPlus (wt0 - ν) := by
  have heq : wt0 - ν = (wt0 - μ) + (μ - ν) := by abel
  rw [heq]
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₂, hc₂⟩ := h2
  refine ⟨fun α => c₁ α + c₂ α, ?_⟩
  simp only [hc₁, hc₂, ← Finset.sum_add_distrib, add_nsmul]

def WeightLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  rd.IsInQPlus (wt - μ)

def ReflectionLT {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (α : Δ.𝔥 →ₗ[R] R) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  α ∈ rd.posRoots ∧ ∃ (n : ℕ), 0 < n ∧ rd.corootPairing wt α = (n : R) ∧ μ = wt - n • α

def BruhatLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ α, ReflectionLT rd α a b) μ wt

section CategoryOResults

variable {Δ : TriangularDecomposition R 𝔤}
variable {rd : PositiveRootData Δ}
variable {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

theorem PBW.weightSpace_spanFinite
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (S : Finset M)
    (hS : LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤)
    (hS_wt : ∀ v ∈ S, ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt)
    (hbnd : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ ν ∈ weights Δ M, ∃ w ∈ bds, rd.IsInQPlus (w - ν))
    (μ : Δ.𝔥 →ₗ[R] R) :
    ∃ (T : Finset (WeightSpace Δ M μ)),
      Submodule.span R (T : Set (WeightSpace Δ M μ)) = ⊤ :=
  pbw_weightSpace_spanFinite S hS hS_wt hbnd μ

theorem CategoryO.weightSpace_finiteDimensional
    (hM : IsCategoryO Δ rd M) (μ : Δ.𝔥 →ₗ[R] R) :
    Module.Finite R (WeightSpace Δ M μ) := by
  classical

  obtain ⟨S, hS_gen⟩ := hM.finitely_generated


  have hwd := hM.weight_decomp
  choose Ss vs hvs using (fun s => hwd s)

  let S' : Finset M := S.biUnion (fun s => (Ss s).image (fun ν => (vs s ν : M)))

  have hS'_wt : ∀ v ∈ S', ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt := by
    intro v hv
    simp only [S', Finset.mem_biUnion, Finset.mem_image] at hv
    obtain ⟨s, _, ν, _, rfl⟩ := hv
    exact ⟨ν, (vs s ν).property⟩

  have hS'_gen : LieSubmodule.lieSpan R 𝔤 (S' : Set M) = ⊤ := by
    rw [eq_top_iff, ← hS_gen]
    apply LieSubmodule.lieSpan_le.mpr
    intro s hs
    have hsum : s = ∑ ν ∈ Ss s, (vs s ν : M) := hvs s
    rw [hsum]
    apply sum_mem
    intro ν hν
    apply LieSubmodule.subset_lieSpan
    show (vs s ν : M) ∈ (S' : Set M)
    simp only [S', Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨s, hs, ν, hν, rfl⟩


  obtain ⟨T, hT⟩ := PBW.weightSpace_spanFinite S' hS'_gen hS'_wt hM.weight_bound μ

  exact Module.Finite.of_fg_top ⟨T, hT⟩

noncomputable def pbw_abelian_iso (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
    [IsLieAbelian L] :
    UniversalEnvelopingAlgebra R L ≃ₐ[R] SymmetricAlgebra R L := by sorry

theorem hilbert_noether_commRing
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {G : Type*} [Group G] [Fintype G]
    (algAct : G →* (A ≃ₐ[R] A))
    (hA_fg : Subalgebra.FG (⊤ : Subalgebra R A)) :
    (Subalgebra.invariants G algAct).FG := by

  letI : MulSemiringAction G A := MulSemiringAction.compHom A algAct
  letI : SMulCommClass G R A := ⟨fun g r a => by
    show (algAct g) (r • a) = r • (algAct g) a
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, Algebra.smul_def]⟩

  haveI : Algebra.FiniteType R A := ⟨hA_fg⟩

  have hfg := hilbert_noether_fg (R := R) (A := A) (G := G)

  have hfg_sub : (FixedPoints.subalgebra R A G).FG :=
    (Subalgebra.fg_iff_finiteType _).mpr hfg

  have heq : FixedPoints.subalgebra R A G = Subalgebra.invariants G algAct := by
    ext a
    simp only [FixedPoints.subalgebra, Subalgebra.invariants, Subalgebra.mem_mk,
      Subsemiring.mem_mk, Submonoid.mem_mk]
    constructor
    · intro ha g; exact ha g
    · intro ha g; exact ha g
  rw [← heq]
  exact hfg_sub

theorem symmetric_algebra_fg_top (R : Type*) [CommRing R]
    (L : Type*) [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    [Module.Free R L] [Module.Finite R L] :
    Subalgebra.FG (⊤ : Subalgebra R (SymmetricAlgebra R L)) := by
  by_cases hR : Nontrivial R
  · have hb := Module.Free.chooseBasis R L
    haveI : Finite (Module.Free.ChooseBasisIndex R L) := Module.Finite.finite_basis hb
    haveI : Algebra.FiniteType R (MvPolynomial (Module.Free.ChooseBasisIndex R L) R) :=
      Algebra.FiniteType.instMvPolynomialOfFinite
    haveI : Algebra.FiniteType R (SymmetricAlgebra R L) :=
      Algebra.FiniteType.equiv ‹Algebra.FiniteType R (MvPolynomial _ R)›
        (SymmetricAlgebra.equivMvPolynomial hb).symm
    exact Algebra.FiniteType.out
  · rw [not_nontrivial_iff_subsingleton] at hR
    haveI := hR
    refine ⟨∅, ?_⟩
    have : Subsingleton (SymmetricAlgebra R L) := by
      have h01 : (0 : R) = 1 := Subsingleton.elim _ _
      constructor; intro a b
      have : ∀ (x : SymmetricAlgebra R L), x = 0 := by
        intro x
        calc x = (1 : R) • x := by simp
          _ = (0 : R) • x := by rw [h01]
          _ = 0 := by simp
      rw [this a, this b]
    ext x
    simp [Subsingleton.elim x (algebraMap R _ 0)]

noncomputable def conjActionThroughPBW
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    {G : Type*} [Group G]
    (act : G →* (UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R L)) :
    G →* (SymmetricAlgebra R L ≃ₐ[R] SymmetricAlgebra R L) where
  toFun g := (pbw_abelian_iso R L).symm.trans ((act g).trans (pbw_abelian_iso R L))
  map_one' := by ext x; simp [AlgEquiv.trans_apply]
  map_mul' g h := by ext x; simp [AlgEquiv.trans_apply, AlgEquiv.mul_apply]

theorem invariantSubalgebra_fg_of_abelian_finiteGroup
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    [Module.Free R L] [Module.Finite R L]
    {G : Type*} [Group G] [Fintype G]
    (act : G →* (UniversalEnvelopingAlgebra R L) ≃ₐ[R] (UniversalEnvelopingAlgebra R L)) :
    (Subalgebra.invariants G act).FG := by

  let φ := pbw_abelian_iso R L
  let act' := conjActionThroughPBW act

  have h_fg_sym := hilbert_noether_commRing act' (symmetric_algebra_fg_top R L)

  have h_map : Subalgebra.map φ.toAlgHom (Subalgebra.invariants G act) =
               Subalgebra.invariants G act' := by
    ext x
    simp only [Subalgebra.mem_map, Subalgebra.invariants, Subalgebra.mem_mk]

    constructor
    · rintro ⟨a, ha, rfl⟩
      intro g
      change (φ.symm.trans ((act g).trans φ)) (φ a) = φ a
      simp [AlgEquiv.trans_apply, ha g]
    · intro hx
      refine ⟨φ.symm x, ?_, by simp⟩
      intro g
      have hg := hx g
      change (φ.symm.trans ((act g).trans φ)) x = x at hg
      simp [AlgEquiv.trans_apply] at hg
      apply φ.injective
      rw [hg]; simp

  rw [← h_map] at h_fg_sym
  exact Subalgebra.fg_of_fg_map _ φ.toAlgHom φ.injective h_fg_sym

theorem chevalley_invariant_finiteType

    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    [Module.Free R Δ.𝔥] [Module.Finite R Δ.𝔥]
    (wg : WeylGroupData Δ) :
    Algebra.FiniteType R ↥(wg.invariantSubalgebra) := by

  haveI : IsLieAbelian Δ.𝔥 := Δ.h_abelian

  haveI : Fintype wg.W := wg.instFintype

  have hfg : wg.invariantSubalgebra.FG :=
    invariantSubalgebra_fg_of_abelian_finiteGroup wg.algAction

  exact (Subalgebra.fg_iff_finiteType wg.invariantSubalgebra).mp hfg

theorem center_UEA_finitelyGenerated_of_HC
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    [Module.Free R Δ.𝔥] [Module.Finite R Δ.𝔥]
    (wg : WeylGroupData Δ) :
    ∃ (S : Finset (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      ∀ z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
        z ∈ Algebra.adjoin R (S : Set _) := by

  have hft_inv := chevalley_invariant_finiteType Δ wg

  have hft_center : Algebra.FiniteType R ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :=
    hft_inv.equiv (HarishChandraIso Δ wg).symm

  obtain ⟨S, hS⟩ := hft_center.1
  exact ⟨S, fun z => hS ▸ Algebra.mem_top⟩

theorem center_UEA_finitelyGenerated
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    [Module.Free R Δ.𝔥] [Module.Finite R Δ.𝔥]
    (wg : WeylGroupData Δ) :
    ∃ (S : Finset (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      ∀ z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
        z ∈ Algebra.adjoin R (S : Set _) := by


  exact center_UEA_finitelyGenerated_of_HC Δ wg

theorem center_element_integral_on_catO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    ∃ (p : Polynomial R), p.Monic ∧
      Polynomial.aeval (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤)) p = 0 := by
  classical


  obtain ⟨S, hS_gen⟩ := hM.finitely_generated
  have hwd := hM.weight_decomp
  choose Ss vs hvs using (fun s => hwd s)

  let S' : Finset M := S.biUnion (fun s => (Ss s).image (fun ν => (vs s ν : M)))

  let Λ : Finset (Δ.𝔥 →ₗ[R] R) := S.biUnion (fun s => Ss s)


  have hS'_wt : ∀ v ∈ S', ∃ wt : Δ.𝔥 →ₗ[R] R, wt ∈ Λ ∧ v ∈ WeightSpace Δ M wt := by
    intro v hv
    simp only [S', Finset.mem_biUnion, Finset.mem_image] at hv
    obtain ⟨s, hs, ν, hν, rfl⟩ := hv
    exact ⟨ν, Finset.mem_biUnion.mpr ⟨s, hs, hν⟩, (vs s ν).property⟩


  have hS'_gen : LieSubmodule.lieSpan R 𝔤 (S' : Set M) = ⊤ := by
    rw [eq_top_iff, ← hS_gen]
    apply LieSubmodule.lieSpan_le.mpr
    intro s hs
    have hsum : s = ∑ ν ∈ Ss s, (vs s ν : M) := hvs s
    rw [hsum]
    apply sum_mem
    intro ν hν
    apply LieSubmodule.subset_lieSpan
    show (vs s ν : M) ∈ (S' : Set M)
    simp only [S', Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨s, hs, ν, hν, rfl⟩


  let E : Submodule R M := ⨆ μ ∈ Λ, WeightSpace Δ M μ


  have hμ_fin : ∀ μ ∈ Λ, Module.Finite R (WeightSpace Δ M μ) :=
    fun μ _ => CategoryO.weightSpace_finiteDimensional hM μ


  have hE_fin : E.FG := by
    apply Submodule.fg_biSup Λ
    intro μ hμ
    have : (⊤ : Submodule R ↥(WeightSpace Δ M μ)).FG := Module.finite_def.mp (hμ_fin μ hμ)
    rwa [Submodule.fg_top] at this


  have hS'_in_E : ∀ v ∈ S', v ∈ E := by
    intro v hv
    obtain ⟨wt, hwt_mem, hv_wt⟩ := hS'_wt v hv
    exact Submodule.mem_iSup_of_mem wt (Submodule.mem_iSup_of_mem hwt_mem hv_wt)


  have hz_preserves_wt : ∀ μ (m : M), m ∈ WeightSpace Δ M μ →
      ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m ∈ WeightSpace Δ M μ := by
    intro μ m hm h


    have hcomm : (z : UniversalEnvelopingAlgebra R 𝔤) *
        UniversalEnvelopingAlgebra.ι R (h : 𝔤) =
        UniversalEnvelopingAlgebra.ι R (h : 𝔤) * (z : UniversalEnvelopingAlgebra R 𝔤) := by
      have hz := z.property
      rw [Subalgebra.mem_center_iff] at hz
      exact (hz _).symm
    rw [← hcompat (h : 𝔤)]


    change (ueaAct (UniversalEnvelopingAlgebra.ι R ↑h) *
        ueaAct (↑z)) m = μ h • (ueaAct (↑z)) m
    rw [← map_mul, hcomm.symm, map_mul]
    change (ueaAct (↑z)) ((ueaAct (UniversalEnvelopingAlgebra.ι R ↑h)) m) = _
    rw [hcompat (h : 𝔤), hm h]
    exact (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤)).map_smul (μ h) m


  have hz_preserves_E : ∀ m ∈ E, ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m ∈ E := by
    intro m hm

    rw [show E = ⨆ μ ∈ Λ, WeightSpace Δ M μ from rfl] at hm ⊢
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hm ⊢
    obtain ⟨f, hf⟩ := hm
    refine ⟨fun μ => ⟨ueaAct (↑z) (f μ), hz_preserves_wt μ _ (f μ).property⟩, ?_⟩
    rw [← hf]
    simp only [map_sum]


  haveI hE_mod_fin : Module.Finite R E := Module.Finite.of_fg hE_fin
  let zE : Module.End R E :=
    (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤)).restrict hz_preserves_E
  obtain ⟨p, hp_monic, hp_aeval⟩ := LinearMap.exists_monic_and_aeval_eq_zero R zE


  have aeval_restrict_val : ∀ (q : Polynomial R) (e : M) (he : e ∈ E),
      (((Polynomial.aeval zE) q) ⟨e, he⟩ : M) =
      (Polynomial.aeval (ueaAct (↑z))) q e := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ hq₁ hq₂ =>
      intro e he
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hq₁ e he, hq₂ e he]
    | monomial n r =>
      intro e he
      simp only [Polynomial.aeval_monomial]
      change ↑((r • (ueaAct (↑z)).restrict hz_preserves_E ^ n) ⟨e, he⟩) =
             (r • ueaAct (↑z) ^ n) e
      simp only [LinearMap.smul_apply, Submodule.coe_smul]
      congr 1
      rw [Module.End.pow_restrict]; rfl


  have aeval_commutes : ∀ (q : Polynomial R) (x : 𝔤),
      Commute ((Polynomial.aeval (ueaAct (↑z))) q)
              (ueaAct (UniversalEnvelopingAlgebra.ι R x)) := by
    intro q x
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ hq₁ hq₂ => rw [map_add]; exact hq₁.add_left hq₂
    | monomial n r =>
      simp only [Polynomial.aeval_monomial]
      have hcomm_end : Commute (ueaAct (↑z)) (ueaAct (UniversalEnvelopingAlgebra.ι R x)) := by
        show ueaAct (↑z) * ueaAct (UniversalEnvelopingAlgebra.ι R x) =
             ueaAct (UniversalEnvelopingAlgebra.ι R x) * ueaAct (↑z)
        rw [← map_mul, ← map_mul]
        congr 1
        have hz := z.property
        rw [Subalgebra.mem_center_iff] at hz
        exact (hz _).symm
      exact (Algebra.commute_algebraMap_left r _).mul_left (hcomm_end.pow_left n)


  refine ⟨p, hp_monic, ?_⟩


  have hp_on_E : ∀ e ∈ E, (Polynomial.aeval (ueaAct (↑z))) p e = 0 := by
    intro e he
    have hzero : ((Polynomial.aeval zE) p) ⟨e, he⟩ = 0 := by
      rw [hp_aeval]; rfl
    rw [← aeval_restrict_val p e he]; exact congrArg Subtype.val hzero


  have hp_lie : ∀ (x : 𝔤) (m : M),
      (Polynomial.aeval (ueaAct (↑z))) p (⁅x, m⁆) =
      ⁅x, (Polynomial.aeval (ueaAct (↑z))) p m⁆ := by
    intro x m'
    rw [← hcompat x, ← hcompat x]

    have hcomm := aeval_commutes p x


    change ((Polynomial.aeval (ueaAct (↑z))) p)
        ((ueaAct (UniversalEnvelopingAlgebra.ι R x)) m') =
      (ueaAct (UniversalEnvelopingAlgebra.ι R x))
        (((Polynomial.aeval (ueaAct (↑z))) p) m')
    exact DFunLike.congr_fun hcomm.eq m'


  ext m
  simp only [LinearMap.zero_apply]

  let pz := (Polynomial.aeval (ueaAct (↑z))) p
  let kerPz : LieSubmodule R 𝔤 M :=
    { toSubmodule := LinearMap.ker pz
      lie_mem := by
        intro x m' hm'
        change m' ∈ LinearMap.ker pz at hm'
        change ⁅x, m'⁆ ∈ LinearMap.ker pz
        rw [LinearMap.mem_ker] at hm' ⊢
        rw [hp_lie x m', hm']
        exact lie_zero x }


  have hS'_in_ker : (S' : Set M) ⊆ (kerPz : Set M) := by
    intro v hv
    show v ∈ LinearMap.ker pz
    rw [LinearMap.mem_ker]
    exact hp_on_E v (hS'_in_E v hv)

  have hspan_le : LieSubmodule.lieSpan R 𝔤 (S' : Set M) ≤ kerPz :=
    LieSubmodule.lieSpan_le.mpr hS'_in_ker

  have hm_in_span : m ∈ LieSubmodule.lieSpan R 𝔤 (S' : Set M) := by
    rw [hS'_gen]; trivial

  have hm_in_ker := hspan_le hm_in_span
  show pz m = 0
  exact (LinearMap.mem_ker.mp hm_in_ker)

theorem CategoryO.center_acts_through_finiteDim_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    [Module.Free R Δ.𝔥] [Module.Finite R Δ.𝔥]
    {rd : PositiveRootData Δ}
    (wg : WeylGroupData Δ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧
      ∀ z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
        ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) ∈ S := by


  let f : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] Module.End R M :=
    ueaAct.comp (Subalgebra.val (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))

  let centerMap : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₗ[R]
      Module.End R M := f.toLinearMap

  have hrange_eq : centerMap.range = Subalgebra.toSubmodule f.range := by
    ext x; simp [LinearMap.mem_range, AlgHom.mem_range, centerMap, f]
  refine ⟨centerMap.range, ?_, ?_⟩
  ·
    apply Module.Finite.of_fg
    rw [hrange_eq]

    letI : CommRing ↥f.range :=
      { Subalgebra.toRing f.range with
        mul_comm := fun ⟨x, hx⟩ ⟨y, hy⟩ => by
          ext
          simp only [MulMemClass.mk_mul_mk]
          obtain ⟨a, rfl⟩ := hx
          obtain ⟨b, rfl⟩ := hy
          simp only [← map_mul, mul_comm] }

    have hft_center : Algebra.FiniteType R ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) := by
      obtain ⟨gens, hgens⟩ := center_UEA_finitelyGenerated (R := R) (𝔤 := 𝔤) Δ wg
      exact ⟨⟨gens, by ext z; simp [hgens z]⟩⟩

    have hft_range : Algebra.FiniteType R ↥f.range :=
      Algebra.FiniteType.of_surjective f.rangeRestrict f.rangeRestrict_surjective

    have hint : Algebra.IsIntegral R ↥f.range := by
      constructor
      intro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := hx

      obtain ⟨p, hp_monic, hp_aeval⟩ := center_element_integral_on_catO hM ueaAct hcompat z


      refine ⟨p, hp_monic, ?_⟩
      show Polynomial.aeval (f.rangeRestrict z) p = 0

      have h1 := AlgHom.congr_fun (Polynomial.aeval_algHom f.rangeRestrict z) p
      simp [AlgHom.comp_apply] at h1
      rw [h1]


      have h2 := AlgHom.congr_fun (Polynomial.aeval_algHom f z) p
      simp [AlgHom.comp_apply] at h2


      have hfz : (Polynomial.aeval (f z)) p = 0 := hp_aeval
      rw [h2] at hfz


      have : (f.rangeRestrict ((Polynomial.aeval z) p)).val = (0 : Module.End R M) := hfz
      exact Subtype.val_injective this

    have hfin : Module.Finite R ↥f.range := @Algebra.IsIntegral.finite R ↥f.range _ _ _ hint hft_range

    have h : (⊤ : Submodule R ↥f.range).FG := Module.finite_def.mp hfin
    have h2 := h.map f.range.val.toLinearMap
    convert h2 using 1
    ext x; simp

  ·
    intro z
    exact LinearMap.mem_range.mpr ⟨z, rfl⟩

def GeneralizedEigenspaceCenter
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    Submodule R M where
  carrier := {m : M | ∀ (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
    ∃ (n : ℕ), ((ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
      chi z • (LinearMap.id : Module.End R M)) ^ n : Module.End R M) m = 0}
  add_mem' := by

    intro a b ha hb z
    obtain ⟨na, hna⟩ := ha z
    obtain ⟨nb, hnb⟩ := hb z
    set T : Module.End R M := ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
      chi z • (LinearMap.id : Module.End R M) with hT_def
    use na + nb

    have hlin := (T ^ (na + nb)).map_add a b
    rw [hlin]

    have ha0 : (T ^ (na + nb)) a = 0 := by
      have h1 : T ^ (na + nb) = T ^ nb * T ^ na := by
        rw [show na + nb = nb + na from Nat.add_comm na nb]; exact pow_add T nb na
      change (T ^ (na + nb)) a = 0
      rw [h1]; show (T ^ nb) ((T ^ na) a) = 0; rw [hna]; exact map_zero _

    have hb0 : (T ^ (na + nb)) b = 0 := by
      have h1 : T ^ (na + nb) = T ^ na * T ^ nb := pow_add T na nb
      change (T ^ (na + nb)) b = 0
      rw [h1]; show (T ^ na) ((T ^ nb) b) = 0; rw [hnb]; exact map_zero _

    rw [ha0, hb0, add_zero]

  zero_mem' := by
    intro z; exact ⟨0, by simp [pow_zero]⟩

  smul_mem' := by
    intro r m hm z
    obtain ⟨n, hn⟩ := hm z
    exact ⟨n, by simp [map_smul, hn]⟩

def IsInCategoryOChi
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) : Prop :=
  IsCategoryO Δ rd M ∧
  GeneralizedEigenspaceCenter M ueaAct chi = ⊤

def GeneralizedEigenspaceCenter.toLieSubmodule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    LieSubmodule R 𝔤 M :=
  { GeneralizedEigenspaceCenter M ueaAct chi with
    lie_mem := by
      intro x m hm z


      obtain ⟨n, hn⟩ := hm z
      use n

      have hcomm_uea : (z : UniversalEnvelopingAlgebra R 𝔤) *
        UniversalEnvelopingAlgebra.ι R x =
        UniversalEnvelopingAlgebra.ι R x * (z : UniversalEnvelopingAlgebra R 𝔤) := by
        have hz := z.property
        rw [Subalgebra.mem_center_iff] at hz
        exact (hz _).symm

      have hcomm_end : ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) *
        ueaAct (UniversalEnvelopingAlgebra.ι R x) =
        ueaAct (UniversalEnvelopingAlgebra.ι R x) *
        ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) := by
        rw [← map_mul, ← map_mul, hcomm_uea]

      set T : Module.End R M := ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
        chi z • (LinearMap.id : Module.End R M) with hT_def
      set X : Module.End R M := ueaAct (UniversalEnvelopingAlgebra.ι R x)

      have hTX : T * X = X * T := by
        simp only [hT_def, sub_mul, mul_sub, hcomm_end]
        congr 1
        ext m₀
        simp [LinearMap.smul_apply, LinearMap.id_apply]

      have hTnX : T ^ n * X = X * T ^ n := Commute.pow_left hTX n

      have hxm : ⁅x, m⁆ = X m := (hcompat x m).symm
      rw [hxm]
      show (T ^ n) (X m) = 0
      have : (T ^ n) (X m) = (T ^ n * X) m := rfl
      rw [this, hTnX]
      show X ((T ^ n) m) = 0
      rw [hn, map_zero] }

lemma GeneralizedEigenspaceCenter.toLieSubmodule_coe
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    (GeneralizedEigenspaceCenter.toLieSubmodule M ueaAct hcompat chi : Submodule R M) =
    GeneralizedEigenspaceCenter M ueaAct chi := rfl

lemma commute_pow_sub_smul_id {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g : Module.End R M) (hcomm : g * f = f * g)
    (c : R) (k : ℕ) (x : M) :
    ((f - c • (LinearMap.id : Module.End R M)) ^ k) (g x) =
    g (((f - c • (LinearMap.id : Module.End R M)) ^ k) x) := by
  have h1 : Commute g (f - c • (LinearMap.id : Module.End R M)) := by
    rw [Commute, SemiconjBy, mul_sub, sub_mul, hcomm]
    congr 1; ext y; simp
  exact congr_fun (congr_arg DFunLike.coe (h1.pow_right k).symm) x

theorem orthogonal_idempotent_decomposition_core
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (actA : A →ₐ[R] Module.End R M)
    (hfg : ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧ ∀ a : A, actA a ∈ S) :
    ∃ (n : ℕ)
      (es : Fin n → Module.End R M)
      (chis : Fin n → (A →ₐ[R] R)),
      (∀ i, es i * es i = es i) ∧
      (∀ i j, i ≠ j → es i * es j = 0) ∧
      (∀ m : M, (∑ i : Fin n, es i) m = m) ∧
      (∀ i (a : A), ∃ (N : ℕ),
        ∀ m : M, ((actA a - chis i a • (LinearMap.id : Module.End R M)) ^ N) (es i m) = 0) ∧
      (∀ i (a : A), es i * actA a = actA a * es i) ∧
      (∀ i j, i ≠ j → ∃ a : A, IsUnit (chis i a - chis j a)) := by sorry

theorem orthogonal_idempotent_decomposition_of_fg_center_action
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (actA : A →ₐ[R] Module.End R M)
    (hfg : ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧ ∀ a : A, actA a ∈ S) :
    ∃ (n : ℕ)
      (es : Fin n → Module.End R M)
      (chis : Fin n → (A →ₐ[R] R)),

      (∀ i, es i * es i = es i) ∧
      (∀ i j, i ≠ j → es i * es j = 0) ∧

      (∀ m : M, (∑ i : Fin n, es i) m = m) ∧

      (∀ i (a : A), ∃ (N : ℕ),
        ∀ m : M, ((actA a - chis i a • (LinearMap.id : Module.End R M)) ^ N) (es i m) = 0) ∧

      (∀ i (a : A), es i * actA a = actA a * es i) ∧


      (∀ i (m : M),
        (∀ (a : A), ∃ N : ℕ, ((actA a - chis i a • (LinearMap.id : Module.End R M)) ^ N) m = 0) →
        es i m = m) := by
  obtain ⟨n, es, chis, hidem, horth, hsum, hgen, hcomm, hdistinct⟩ :=
    orthogonal_idempotent_decomposition_core actA hfg
  exact ⟨n, es, chis, hidem, horth, hsum, hgen, hcomm, fun i m hm => by

    suffices h_zero : ∀ j, j ≠ i → es j m = 0 by
      have hm_eq : m = ∑ j : Fin n, es j m := by
        rw [← LinearMap.sum_apply]; exact (hsum m).symm
      conv_rhs => rw [hm_eq]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun j _ hji => h_zero j hji)]
    intro j hji

    obtain ⟨a₀, ha₀⟩ := hdistinct i j (Ne.symm hji)

    obtain ⟨Nj, hNj⟩ := hgen j a₀

    obtain ⟨Ni, hNi⟩ := hm a₀

    have h1 : ((actA a₀ - chis i a₀ • (LinearMap.id : Module.End R M)) ^ Ni) (es j m) = 0 := by
      rw [commute_pow_sub_smul_id (actA a₀) (es j) (hcomm j a₀) (chis i a₀) Ni m,
        hNi, map_zero]
    have h2 : ((actA a₀ - chis j a₀ • (LinearMap.id : Module.End R M)) ^ Nj) (es j m) = 0 :=
      hNj m

    have hcop := (Polynomial.isCoprime_X_sub_C_of_isUnit_sub ha₀).pow (m := Ni) (n := Nj)
    have hdisj := Polynomial.disjoint_ker_aeval_of_isCoprime (actA a₀) hcop

    have hx1 : es j m ∈ (Polynomial.aeval (actA a₀)
        ((Polynomial.X - Polynomial.C (chis i a₀)) ^ Ni)).ker := by
      rw [LinearMap.mem_ker, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one]; exact h1
    have hx2 : es j m ∈ (Polynomial.aeval (actA a₀)
        ((Polynomial.X - Polynomial.C (chis j a₀)) ^ Nj)).ker := by
      rw [LinearMap.mem_ker, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one]; exact h2
    exact (Submodule.eq_bot_iff _).mp hdisj.eq_bot (es j m) ⟨hx1, hx2⟩⟩

theorem artinian_generalized_eigenspace_decomposition
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hfindim : ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧
      ∀ z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
        ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) ∈ S) :
    ∃ (n : ℕ)
      (chis : Fin n → (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)),

      (∀ i j, i ≠ j → Disjoint
        (GeneralizedEigenspaceCenter M ueaAct (chis i))
        (GeneralizedEigenspaceCenter M ueaAct (chis j))) ∧

      (⨆ i, GeneralizedEigenspaceCenter M ueaAct (chis i)) = ⊤ := by


  let centerAlg := Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)
  let actCenter : centerAlg →ₐ[R] Module.End R M :=
    ueaAct.comp (Subalgebra.val centerAlg)

  have hfg : ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧ ∀ a : centerAlg, actCenter a ∈ S := by
    obtain ⟨S, hS_fin, hS_mem⟩ := hfindim
    exact ⟨S, hS_fin, fun a => hS_mem a⟩

  obtain ⟨n, es, chis, hidem, horth, hsum, hgen, hcomm, hfix⟩ :=
    orthogonal_idempotent_decomposition_of_fg_center_action actCenter hfg

  have hei_in_gen : ∀ i (m : M),
      es i m ∈ GeneralizedEigenspaceCenter M ueaAct (chis i) := by
    intro i m z
    have hact_eq : actCenter z = ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) := rfl
    obtain ⟨N, hN⟩ := hgen i z
    use N
    rw [← hact_eq]
    exact hN m

  have hfix_gen : ∀ i (m : M),
      m ∈ GeneralizedEigenspaceCenter M ueaAct (chis i) → es i m = m := by
    intro i m hm
    apply hfix i m
    intro a


    exact hm a
  refine ⟨n, chis, ?_, ?_⟩
  ·


    intro i j hij
    rw [Submodule.disjoint_def]
    intro m hmi hmj
    have h1 : es i m = m := hfix_gen i m hmi
    have h2 : es j m = m := hfix_gen j m hmj

    have h3 : (es j * es i) m = 0 := by
      rw [horth j i (Ne.symm hij)]
      simp [LinearMap.zero_apply]

    rw [show (es j * es i) m = es j (es i m) from rfl, h1] at h3

    rw [h2] at h3
    exact h3
  ·
    rw [eq_top_iff]
    intro m _

    have hm_sum : m = ∑ k : Fin n, es k m := by
      symm
      have := hsum m
      rwa [LinearMap.sum_apply] at this
    rw [hm_sum]
    apply Submodule.sum_mem
    intro k _
    exact Submodule.mem_iSup_of_mem k (hei_in_gen k m)

theorem CategoryO.infinitesimalCharacter_decomposition
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    [Module.Free R Δ.𝔥] [Module.Finite R Δ.𝔥]
    {rd : PositiveRootData Δ}
    (wg : WeylGroupData Δ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    ∃ (n : ℕ)
      (chis : Fin n → (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R))
      (N : Fin n → LieSubmodule R 𝔤 M),

      (∀ i j, i ≠ j → Disjoint (N i) (N j)) ∧

      (⨆ i, N i) = ⊤ ∧

      (∀ i, (N i : Submodule R M) = GeneralizedEigenspaceCenter M ueaAct (chis i)) := by

  have hfindim := CategoryO.center_acts_through_finiteDim_quotient wg hM ueaAct hcompat


  obtain ⟨n, chis, hdisj_sub, hspan_sub⟩ :=
    artinian_generalized_eigenspace_decomposition ueaAct hfindim

  refine ⟨n, chis,
    fun i => GeneralizedEigenspaceCenter.toLieSubmodule M ueaAct hcompat (chis i),
    ?_, ?_, ?_⟩
  ·
    intro i j hij
    rw [← LieSubmodule.disjoint_toSubmodule]
    simp only [GeneralizedEigenspaceCenter.toLieSubmodule_coe]
    exact hdisj_sub i j hij
  ·
    rw [← LieSubmodule.iSup_toSubmodule_eq_top]
    simp only [GeneralizedEigenspaceCenter.toLieSubmodule_coe]
    exact hspan_sub
  ·
    intro i
    exact GeneralizedEigenspaceCenter.toLieSubmodule_coe M ueaAct hcompat (chis i)

noncomputable def idealStepFilt
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) (N : Submodule R M) : Submodule R M :=
  ⨆ z : ι, Submodule.map (T z) N

noncomputable def idealChainFilt
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) : ℕ → Submodule R M
  | 0 => ⊤
  | n + 1 => idealStepFilt T (idealChainFilt T n)

theorem locally_nilpotent_ideal_chain_terminates
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*}
    (T : ι → Module.End R M)
    (hcomm : ∀ (z₁ z₂ : ι), T z₁ ∘ₗ T z₂ = T z₂ ∘ₗ T z₁)
    (hfin : ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧ ∀ z : ι, T z ∈ S)
    (hnil : ∀ (z : ι) (m : M), ∃ n : ℕ, (T z ^ n) m = 0) :
    ∃ N : ℕ, idealChainFilt T N = ⊥ := by sorry

lemma idealChainFilt_antitone
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) :
    ∀ n : ℕ, idealChainFilt T (n + 1) ≤ idealChainFilt T n := by
  intro n; induction n with
  | zero => exact le_top
  | succ n ih => exact iSup_mono (fun z => Submodule.map_mono ih)

lemma mem_idealChainFilt_succ
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) (n : ℕ) (z : ι) (m : M)
    (hm : m ∈ idealChainFilt T n) : T z m ∈ idealChainFilt T (n + 1) :=
  Submodule.mem_iSup_of_mem z (Submodule.mem_map.mpr ⟨m, hm, rfl⟩)

lemma idealChainFilt_lie_stable
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {ι : Type*}
    (T : ι → Module.End R M)
    (hcomm : ∀ (x : 𝔤) (z : ι) (m : M), ⁅x, T z m⁆ = T z ⁅x, m⁆)
    (n : ℕ) : ∀ (x : 𝔤) (m : M),
    m ∈ idealChainFilt T n → ⁅x, m⁆ ∈ idealChainFilt T n := by
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro xl m hm
    change m ∈ idealStepFilt T (idealChainFilt T k) at hm
    change ⁅xl, m⁆ ∈ idealStepFilt T (idealChainFilt T k)
    simp only [idealStepFilt] at hm ⊢
    apply Submodule.iSup_induction
      (motive := fun y => ⁅xl, y⁆ ∈ ⨆ z, Submodule.map (T z) (idealChainFilt T k))
      (fun z => Submodule.map (T z) (idealChainFilt T k)) hm
    · intro z y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨m₀, hm₀, rfl⟩ := hy
      rw [hcomm]
      apply Submodule.mem_iSup_of_mem z
      exact Submodule.mem_map.mpr ⟨⁅xl, m₀⁆, ih xl m₀ hm₀, rfl⟩
    · simp [lie_zero]
    · intro y₁ y₂ hy₁ hy₂
      rw [lie_add]
      exact Submodule.add_mem _ hy₁ hy₂

theorem artinian_madic_filtration
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (hfindim : ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧
      ∀ z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
        ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) ∈ S)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (hchi : GeneralizedEigenspaceCenter M ueaAct chi = ⊤) :
    ∃ (k : ℕ) (F : Fin (k + 1) → Submodule R M),

      F ⟨0, Nat.zero_lt_succ k⟩ = ⊤ ∧
      F ⟨k, lt_add_one k⟩ = ⊥ ∧

      (∀ (i : Fin k), F i.castSucc ≥ F i.succ) ∧

      (∀ (i : Fin (k + 1)) (x : 𝔤) (m : M), m ∈ F i → ⁅x, m⁆ ∈ F i) ∧

      (∀ (i : Fin k) (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
         (m : M), m ∈ F i.castSucc →
         ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m - chi z • m ∈ F i.succ) := by

  set Tz : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) → Module.End R M :=
    fun z => ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
      chi z • (LinearMap.id : Module.End R M) with hTz_def

  have hTz_fin : ∃ (S : Submodule R (Module.End R M)),
      Module.Finite R S ∧ ∀ z, Tz z ∈ S := by
    obtain ⟨S, hfin, hS⟩ := hfindim
    have : Module.Finite R ↥(Submodule.span R ({LinearMap.id} : Set (Module.End R M))) :=
      Module.Finite.span_of_finite _ (Set.finite_singleton _)
    refine ⟨S ⊔ Submodule.span R {LinearMap.id}, Submodule.finite_sup _ _, ?_⟩
    intro z
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (hS z))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span rfl)))

  have hTz_nil : ∀ z m, ∃ n : ℕ, (Tz z ^ n) m = 0 := by
    intro z m
    have hmem : m ∈ GeneralizedEigenspaceCenter M ueaAct chi := by rw [hchi]; trivial
    exact hmem z


  have hTz_comm_ops : ∀ z₁ z₂, Tz z₁ ∘ₗ Tz z₂ = Tz z₂ ∘ₗ Tz z₁ := by
    intro z₁ z₂


    have hTz_eq : ∀ z, Tz z = ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
        algebraMap R (Module.End R M) (chi z) := by
      intro z
      simp only [hTz_def, Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]

    have hc : Commute (ueaAct (↑z₁ : UniversalEnvelopingAlgebra R 𝔤))
                       (ueaAct (↑z₂ : UniversalEnvelopingAlgebra R 𝔤)) := by
      show ueaAct (↑z₁) * ueaAct (↑z₂) = ueaAct (↑z₂) * ueaAct (↑z₁)
      rw [← map_mul, ← map_mul]
      congr 1
      exact ((Subalgebra.mem_center_iff.mp z₁.prop) ↑z₂).symm

    have hcomm : Commute (Tz z₁) (Tz z₂) := by
      rw [hTz_eq, hTz_eq]
      exact (hc.sub_right (Algebra.commute_algebraMap_right (chi z₂) _)).sub_left
        (Algebra.commute_algebraMap_left (chi z₁) _)


    show Tz z₁ * Tz z₂ = Tz z₂ * Tz z₁
    exact hcomm


  obtain ⟨N, hN⟩ := locally_nilpotent_ideal_chain_terminates Tz hTz_comm_ops hTz_fin hTz_nil


  have hTz_comm : ∀ (x : 𝔤) (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
      (m : M), ⁅x, Tz z m⁆ = Tz z ⁅x, m⁆ := by
    intro x z m
    simp only [hTz_def, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

    rw [lie_sub, lie_smul]


    congr 1
    have hz_center := z.prop
    rw [Subalgebra.mem_center_iff] at hz_center
    rw [← hcompat x m, ← hcompat x (ueaAct ↑z m)]
    have h1 : ueaAct (UniversalEnvelopingAlgebra.ι R x) (ueaAct ↑z m) =
              ueaAct (UniversalEnvelopingAlgebra.ι R x * ↑z) m := by rw [map_mul]; rfl
    have h2 : ueaAct ↑z (ueaAct (UniversalEnvelopingAlgebra.ι R x) m) =
              ueaAct (↑z * UniversalEnvelopingAlgebra.ι R x) m := by rw [map_mul]; rfl
    rw [h1, h2, hz_center]

  refine ⟨N, fun i => idealChainFilt Tz i.val, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rfl
  ·
    exact hN
  ·
    intro i
    exact idealChainFilt_antitone Tz i.val
  ·
    intro i x m hm
    exact idealChainFilt_lie_stable Tz hTz_comm i.val x m hm
  ·
    intro i z m hm
    exact mem_idealChainFilt_succ Tz i.val z m hm

theorem CategoryO.detecting_submodule_gives_chain_bound
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (E : Submodule R M)
    (hdetect : ∀ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ →
      ∃ x, x ∈ (N₂ : Submodule R M) ⊓ E ∧ x ∉ (N₁ : Submodule R M))
    (n : ℕ)
    (hE_bound : ∀ (chain : Fin (n + 2) → Submodule R M),
      (∀ i, chain i ≤ E) → StrictMono chain → False) :
    ∀ (chain : Fin (n + 2) → LieSubmodule R 𝔤 M), StrictMono chain → False := by
  intro chain hchain

  let chain' : Fin (n + 2) → Submodule R M := fun i => (chain i : Submodule R M) ⊓ E

  have hchain' : StrictMono chain' := by
    intro i j hij
    have hlt := hchain hij
    obtain ⟨x, hx_mem, hx_not⟩ := hdetect (chain i) (chain j) hlt
    apply lt_of_le_of_ne
    · intro y hy
      exact ⟨(hchain.monotone hij.le) hy.1, hy.2⟩
    · intro heq
      have hxi : x ∈ chain' i := by rw [heq]; exact hx_mem
      exact hx_not (Submodule.mem_inf.mp hxi).1

  have hle : ∀ i, chain' i ≤ E := fun i => inf_le_right

  exact hE_bound chain' hle hchain'

theorem section4_weightSpace_iSupIndep
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    iSupIndep fun μ : Δ.𝔥 →ₗ[R] R => (WeightSpace Δ M μ : Submodule R M) := by
  haveI : IsLieAbelian Δ.𝔥 := Δ.h_abelian
  simp_rw [fun μ => weightSpace_eq_mathlib_weightSpace (Δ := Δ) (M := M) μ]
  exact ((LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace R Δ.𝔥 M)).comp
    DFunLike.coe_injective).mono
    fun χ => LieModule.weightSpace_le_genWeightSpace M (χ ·)

theorem weightSpace_iSupIndep
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    iSupIndep fun μ : Δ.𝔥 →ₗ[R] R => (WeightSpace Δ M μ : Submodule R M) :=
  section4_weightSpace_iSupIndep

theorem weightSpace_sum_eq_zero_components
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ)
    (hsum : ∑ μ ∈ S, (v μ : M) = 0)
    (μ : Δ.𝔥 →ₗ[R] R) (hμ : μ ∈ S) :
    (v μ : M) = 0 := by
  have hindep := @weightSpace_iSupIndep R _ 𝔤 _ _ Δ M _ _ _ _
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero] at hindep
  exact hindep S (fun σ => (v σ : M)) (fun σ _ => (v σ).property) hsum μ hμ

theorem lieSubmodule_weight_decomp
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hwd : HasWeightDecomposition Δ M)
    (N : LieSubmodule R 𝔤 M)
    (m : M) (hm : m ∈ N) :
    ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)) (w : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ),
      m = ∑ μ ∈ T, (w μ : M) ∧ ∀ μ ∈ T, (w μ : M) ∈ N := by

  obtain ⟨S, v, hdecomp⟩ := hwd m


  refine ⟨S, v, hdecomp, fun ν hν => ?_⟩


  have mk_weight : ∀ σ : Δ.𝔥 →ₗ[R] R,
      (LieSubmodule.Quotient.mk' N (v σ : M)) ∈ WeightSpace Δ (M ⧸ N) σ := by
    intro σ h


    rw [show ⁅(h : 𝔤), LieSubmodule.Quotient.mk' N (v σ : M)⁆ =
        LieSubmodule.Quotient.mk' N ⁅(h : 𝔤), (v σ : M)⁆ from rfl]

    rw [(v σ).property h]


    exact map_smul (LieSubmodule.Quotient.mk' N).toLinearMap (σ h) (v σ : M)

  let qv : (σ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ (M ⧸ N) σ :=
    fun σ => ⟨LieSubmodule.Quotient.mk' N (v σ : M), mk_weight σ⟩

  have hsum : ∑ σ ∈ S, (qv σ : M ⧸ N) = 0 := by
    simp only [qv]

    rw [show ∑ σ ∈ S, (LieSubmodule.Quotient.mk' N (v σ : M) : M ⧸ N) =
        LieSubmodule.Quotient.mk' N (∑ σ ∈ S, (v σ : M)) from
      (map_sum (LieSubmodule.Quotient.mk' N).toLinearMap (fun σ => (v σ : M)) S).symm]
    rw [← hdecomp]
    exact (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr hm

  have hν_zero := weightSpace_sum_eq_zero_components S qv hsum ν hν

  simp only [qv] at hν_zero
  rwa [LieSubmodule.Quotient.mk_eq_zero (N := N)] at hν_zero

theorem weightDecomp_component_mem_lieSubmodule
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hwd : HasWeightDecomposition Δ M)
    (N : LieSubmodule R 𝔤 M)
    (m : M) (hm : m ∈ N)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ)
    (hdecomp : m = ∑ μ ∈ S, (v μ : M))
    (μ : Δ.𝔥 →ₗ[R] R) (hμ : μ ∈ S) :
    (v μ : M) ∈ N := by
  classical

  obtain ⟨T, w, hdecomp_w, hw_mem⟩ := lieSubmodule_weight_decomp hwd N m hm

  let d : (ν : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M ν := fun ν =>
    ⟨(if ν ∈ S then (v ν : M) else 0) - (if ν ∈ T then (w ν : M) else 0),
     (WeightSpace Δ M ν).sub_mem
       (by split_ifs with h; exact (v ν).property; exact (WeightSpace Δ M ν).zero_mem)
       (by split_ifs with h; exact (w ν).property; exact (WeightSpace Δ M ν).zero_mem)⟩

  have hdsum : ∑ ν ∈ S ∪ T, (d ν : M) = 0 := by
    simp only [d, sub_eq_add_neg]
    rw [Finset.sum_add_distrib]

    have hv_sum : ∑ ν ∈ S ∪ T, (if ν ∈ S then (v ν : M) else 0) = ∑ ν ∈ S, (v ν : M) := by
      rw [← Finset.sum_filter]
      congr 1; ext ν; simp [Finset.mem_filter, Finset.mem_union]; tauto

    have hw_sum : ∑ ν ∈ S ∪ T, (-(if ν ∈ T then (w ν : M) else 0)) = -(∑ ν ∈ T, (w ν : M)) := by
      conv_lhs => arg 2; ext ν; rw [apply_ite Neg.neg, neg_zero]

      rw [← Finset.sum_filter]
      have hfilt : Finset.filter (fun a => a ∈ T) (S ∪ T) = T := by
        ext ν; simp [Finset.mem_filter, Finset.mem_union]; tauto
      rw [hfilt, Finset.sum_neg_distrib]
    rw [hv_sum, hw_sum, ← hdecomp, ← hdecomp_w, add_neg_cancel]

  have hd_zero := weightSpace_sum_eq_zero_components (S ∪ T) d hdsum μ
    (Finset.mem_union_left T hμ)

  simp only [d] at hd_zero

  rw [if_pos hμ] at hd_zero
  rw [sub_eq_zero] at hd_zero
  rw [hd_zero]
  split_ifs with h
  · exact hw_mem μ h
  · exact N.zero_mem

theorem pbw_lieSubmodule_wellFoundedGT
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hfg : ∃ (S : Finset M), LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤) :
    WellFoundedGT (LieSubmodule R 𝔤 M) := by sorry

theorem lieSubmodule_finitelyGenerated
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hfg : ∃ (S : Finset M), LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤)
    (N : LieSubmodule R 𝔤 M) :
    ∃ (S : Finset N), LieSubmodule.lieSpan R 𝔤 (S : Set N) = ⊤ := by

  have hWF_M : WellFoundedGT (LieSubmodule R 𝔤 M) := pbw_lieSubmodule_wellFoundedGT hfg

  have hmap_sm : StrictMono (LieSubmodule.map N.incl) :=
    Monotone.strictMono_of_injective
      (fun _ _ h => LieSubmodule.map_mono h)
      (LieSubmodule.map_injective_of_injective Subtype.val_injective)
  have hWF_N : WellFoundedGT (LieSubmodule R 𝔤 ↑N) := hmap_sm.wellFoundedGT

  have hcompact : ∀ k : LieSubmodule R 𝔤 ↑N, IsCompactElement k := by
    rwa [← CompleteLattice.isSupFiniteCompact_iff_all_elements_compact,
         ← CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact]

  have htop_le : (⊤ : LieSubmodule R 𝔤 ↑N) ≤ ⨆ (m : ↑N), LieSubmodule.lieSpan R 𝔤 {m} := by
    intro x _
    apply SetLike.le_def.mp (le_iSup _ x)
    exact LieSubmodule.subset_lieSpan rfl

  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
    (LieSubmodule R 𝔤 ↑N) (hcompact ⊤) (fun m : ↑N => LieSubmodule.lieSpan R 𝔤 {m}) htop_le

  refine ⟨s, le_antisymm le_top ?_⟩
  calc (⊤ : LieSubmodule R 𝔤 ↑N)
      ≤ ⨆ m ∈ s, LieSubmodule.lieSpan R 𝔤 {m} := hs
    _ ≤ LieSubmodule.lieSpan R 𝔤 (s : Set ↑N) :=
        iSup₂_le fun m hm =>
          LieSubmodule.lieSpan_mono (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr hm))

theorem IsCategoryO_lieSubmodule
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (N : LieSubmodule R 𝔤 M) :
    IsCategoryO Δ rd N where
  finitely_generated := lieSubmodule_finitelyGenerated hM.finitely_generated N
  weight_decomp := by
    intro ⟨m, hm⟩
    obtain ⟨S, v, hdecomp, hv_mem⟩ := lieSubmodule_weight_decomp hM.weight_decomp N m hm
    classical

    let w : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ (↥N) μ := fun μ =>
      if hmem : μ ∈ S then
        ⟨⟨(v μ : M), hv_mem μ hmem⟩, fun h => by

          apply Subtype.ext


          simp only [LieSubmodule.coe_bracket]
          exact (v μ).property h⟩
      else
        ⟨0, (WeightSpace Δ (↥N) μ).zero_mem⟩
    refine ⟨S, w, ?_⟩

    apply Subtype.ext


    simp only [AddSubmonoidClass.coe_finset_sum]


    conv_lhs => rw [hdecomp]
    apply Finset.sum_congr rfl
    intro μ hmem
    simp only [w, dif_pos hmem]

  weight_bound := by
    obtain ⟨bds, hbds⟩ := hM.weight_bound
    refine ⟨bds, fun μ hμ_wt => ?_⟩
    apply hbds μ

    intro habs
    apply hμ_wt

    rw [eq_bot_iff]
    intro ⟨n, hn_mem⟩ hn_wt


    have hmem_M : n ∈ WeightSpace Δ M μ := by
      intro h
      have := hn_wt h


      have := congr_arg Subtype.val this
      simp only [LieSubmodule.coe_bracket] at this
      exact this
    rw [eq_bot_iff] at habs
    have := habs hmem_M
    exact Subtype.ext this

theorem IsCategoryO_quotient
    {R : Type*} [Field R]
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
    apply hμ; clear hμ
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z q
    obtain ⟨S, v, hm⟩ := hXO.weight_decomp m
    have mk_wt : ∀ ν, (LieSubmodule.Quotient.mk' Z (v ν : X)) ∈
        WeightSpace Δ (X ⧸ Z) ν := by
      intro ν h
      rw [← LieModuleHom.map_lie, (v ν).prop h]
      exact map_smul (LieSubmodule.Quotient.mk' Z).toLinearMap (ν h) (v ν : X)
    classical
    let S' := {μ} ∪ S
    let w : (ν : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ (X ⧸ Z) ν := fun ν =>
      ⟨(if ν ∈ S then (LieSubmodule.Quotient.mk' Z (v ν : X)) else 0) -
       (if ν = μ then LieSubmodule.Quotient.mk' Z m else 0),
       (WeightSpace Δ (X ⧸ Z) ν).sub_mem
         (by split_ifs with h
             · exact mk_wt ν
             · exact (WeightSpace Δ (X ⧸ Z) ν).zero_mem)
         (by split_ifs with h
             · exact h ▸ hq
             · exact (WeightSpace Δ (X ⧸ Z) ν).zero_mem)⟩
    have hsum : ∑ ν ∈ S', (w ν : X ⧸ Z) = 0 := by
      simp only [w, S']
      rw [Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have hlhs : (∑ x ∈ {μ} ∪ S, (if x ∈ S then
            (LieSubmodule.Quotient.mk' Z) ↑(v x) else 0)) =
          ∑ x ∈ S, (LieSubmodule.Quotient.mk' Z) ↑(v x) := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp [Finset.mem_filter]
        tauto
      have hrhs : (∑ x ∈ {μ} ∪ S, (if x = μ then
            (LieSubmodule.Quotient.mk' Z) m else 0)) =
          (LieSubmodule.Quotient.mk' Z) m := by
        rw [Finset.sum_ite_eq']
        simp
      rw [hlhs, hrhs]
      conv_rhs => rw [hm]
      rw [map_sum]
    have hwμ := weightSpace_sum_eq_zero_components S' w hsum μ
      (Finset.mem_union_left S (Finset.mem_singleton_self μ))
    simp only [w] at hwμ
    simp only [if_true] at hwμ
    rw [sub_eq_zero] at hwμ


    split_ifs at hwμ with h
    ·

      have hv_zero : (v μ : X) = 0 := by
        rw [eq_bot_iff] at hbot
        exact hbot (v μ).property
      rw [hv_zero, map_zero] at hwμ
      exact hwμ.symm
    ·
      exact hwμ.symm

lemma CategoryO.subquotient_has_weight_vector
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (N₁ N₂ : LieSubmodule R 𝔤 M) (hlt : N₁ < N₂) :
    ∃ γ, ∃ x, x ∈ (N₂ : Submodule R M) ⊓ WeightSpace Δ M γ ∧
      x ∉ (N₁ : Submodule R M) := by

  obtain ⟨x, hx_N2, hx_N1⟩ := SetLike.exists_of_lt hlt

  obtain ⟨S, v, hdecomp⟩ := hM.weight_decomp x


  by_contra h_all
  push Not at h_all

  apply hx_N1

  rw [hdecomp]
  apply (N₁ : Submodule R M).sum_mem
  intro μ hμS

  have hv_N2 : (v μ : M) ∈ N₂ :=
    weightDecomp_component_mem_lieSubmodule hM.weight_decomp N₂ x hx_N2 S v hdecomp μ hμS

  have hv_wt : (v μ : M) ∈ WeightSpace Δ M μ := (v μ).property

  exact h_all μ (v μ : M) ⟨hv_N2, hv_wt⟩

theorem PositiveRootData.qPlus_cone_inter_finite
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a b : Δ.𝔥 →ₗ[R] R) :
    ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ γ, rd.IsInQPlus (a - γ) → rd.IsInQPlus (b - γ) → γ ∈ T :=
  rd.cone_inter_finite a b

theorem casimir_coset_weight_finite
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (wt : Δ.𝔥 →ₗ[R] R) :
    ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ γ, γ ∈ weights Δ M → rd.IsInQPlus (wt - γ) → γ ∈ T := by
  classical

  obtain ⟨bds, hbds⟩ := hM.weight_bound


  let Tw : (Δ.𝔥 →ₗ[R] R) → Finset (Δ.𝔥 →ₗ[R] R) :=
    fun w => (rd.qPlus_cone_inter_finite w wt).choose
  have hTw : ∀ w γ, rd.IsInQPlus (w - γ) → rd.IsInQPlus (wt - γ) → γ ∈ Tw w :=
    fun w => (rd.qPlus_cone_inter_finite w wt).choose_spec

  refine ⟨bds.biUnion Tw, fun γ hγ_wt hγ_qplus => ?_⟩

  obtain ⟨w, hw_mem, hw_qplus⟩ := hbds γ hγ_wt

  exact Finset.mem_biUnion.mpr ⟨w, hw_mem, hTw w γ hw_qplus hγ_qplus⟩

lemma CategoryO.casimir_weight_finiteness
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ γ, (∃ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ ∧
        ∃ x, x ∈ (N₂ : Submodule R M) ⊓ WeightSpace Δ M γ ∧
          x ∉ (N₁ : Submodule R M)) → γ ∈ S := by
  classical

  obtain ⟨bds, hbds⟩ := hM.weight_bound


  choose Twt hTwt using fun wt => casimir_coset_weight_finite Δ rd M hM wt

  refine ⟨bds.biUnion Twt, fun γ hγ => ?_⟩

  obtain ⟨N₁, N₂, hlt, x, hx_mem, hx_not⟩ := hγ

  have hx_wt : x ∈ (WeightSpace Δ M γ : Submodule R M) :=
    (Submodule.mem_inf.mp hx_mem).2

  have hx_ne : x ≠ 0 := by
    intro h; apply hx_not; rw [h]; exact (N₁ : Submodule R M).zero_mem
  have hγ_wt : γ ∈ weights Δ M := by
    show WeightSpace Δ M γ ≠ ⊥
    intro h
    have : x ∈ (⊥ : Submodule R M) := h ▸ hx_wt
    simp at this
    exact hx_ne this

  obtain ⟨wt, hwt_mem, hwt_qplus⟩ := hbds γ hγ_wt

  have hγ_in_Twt : γ ∈ Twt wt := (hTwt wt) γ hγ_wt hwt_qplus

  exact Finset.mem_biUnion.mpr ⟨wt, hwt_mem, hγ_in_Twt⟩

theorem CategoryO.casimir_singular_weight_detection
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ →
        ∃ γ ∈ S, ∃ x, x ∈ (N₂ : Submodule R M) ⊓ WeightSpace Δ M γ ∧
          x ∉ (N₁ : Submodule R M) := by

  obtain ⟨S, hS_finite⟩ := CategoryO.casimir_weight_finiteness hM
  exact ⟨S, fun N₁ N₂ hlt => by

    obtain ⟨γ, x, hx_mem, hx_not⟩ := CategoryO.subquotient_has_weight_vector hM N₁ N₂ hlt

    exact ⟨γ, hS_finite γ ⟨N₁, N₂, hlt, x, hx_mem, hx_not⟩, x, hx_mem, hx_not⟩⟩

lemma strictMono_fin_le_val {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) :
    ∀ i : Fin n, i.val ≤ f i := by
  intro ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hj : j < n := by omega
    have h1 : f ⟨j, hj⟩ < f ⟨j + 1, hi⟩ := hf (Fin.mk_lt_mk.mpr (by omega))
    have h2 : j ≤ f ⟨j, hj⟩ := ih hj
    show j + 1 ≤ f ⟨j + 1, hi⟩; omega

theorem findim_submodule_chain_bound
    {K : Type*} [DivisionRing K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (E : Submodule K V) [FiniteDimensional K E] :
    ∀ (chain : Fin (Module.finrank K E + 2) → Submodule K V),
      (∀ i, chain i ≤ E) → StrictMono chain → False := by
  intro chain hle hmon
  have hfd : ∀ i, FiniteDimensional K ↥(chain i) :=
    fun i => Submodule.finiteDimensional_of_le (hle i)
  have hbound : ∀ i, Module.finrank K ↥(chain i) ≤ Module.finrank K E :=
    fun i => Submodule.finrank_mono (hle i)
  have hfm : StrictMono (fun i => Module.finrank K ↥(chain i)) := by
    intro a b hab; exact Submodule.finrank_lt_finrank_of_lt (hmon hab)
  have hge := strictMono_fin_le_val hfm ⟨Module.finrank K E + 1, by omega⟩
  have hle' := hbound ⟨Module.finrank K E + 1, by omega⟩
  simp at hge; omega

theorem CategoryO.weightSpaceSum_chain_bound
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (S : Finset (Δ.𝔥 →ₗ[R] R)) :
    ∃ (n : ℕ), ∀ (chain : Fin (n + 2) → Submodule R M),
      (∀ i, chain i ≤ ⨆ μ ∈ S, WeightSpace Δ M μ) → StrictMono chain → False := by

  have hE_fd : FiniteDimensional R ↥(⨆ μ ∈ S, WeightSpace Δ M μ) := by
    have hfg : (⨆ μ ∈ S, WeightSpace Δ M μ).FG := by
      apply Submodule.fg_biSup S
      intro μ _
      have hfin := CategoryO.weightSpace_finiteDimensional hM μ
      have htop : (⊤ : Submodule R (WeightSpace Δ M μ)).FG := Module.finite_def.mp hfin
      rwa [Submodule.fg_top] at htop
    change Module.Finite R ↥(⨆ μ ∈ S, WeightSpace Δ M μ)
    rw [Module.finite_def, Submodule.fg_top]; exact hfg

  exact ⟨Module.finrank R ↥(⨆ μ ∈ S, WeightSpace Δ M μ),
         findim_submodule_chain_bound _⟩

theorem CategoryO.casimir_detecting_submodule
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    ∃ (E : Submodule R M) (n : ℕ),
      (∀ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ →
        ∃ x, x ∈ (N₂ : Submodule R M) ⊓ E ∧ x ∉ (N₁ : Submodule R M)) ∧
      (∀ (chain : Fin (n + 2) → Submodule R M),
        (∀ i, chain i ≤ E) → StrictMono chain → False) := by

  obtain ⟨S, hS_detect⟩ := CategoryO.casimir_singular_weight_detection hM

  obtain ⟨n, hE_bound⟩ := CategoryO.weightSpaceSum_chain_bound hM S

  refine ⟨⨆ μ ∈ S, WeightSpace Δ M μ, n, ?_, ?_⟩

  · intro N₁ N₂ hlt
    obtain ⟨γ, hγS, x, hx_mem, hx_not⟩ := hS_detect N₁ N₂ hlt
    exact ⟨x, Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx_mem).1,
      Submodule.mem_iSup_of_mem γ (Submodule.mem_iSup_of_mem hγS
        (Submodule.mem_inf.mp hx_mem).2)⟩, hx_not⟩

  · exact hE_bound

theorem CategoryO.finite_length
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    ∃ (n : ℕ), ∀ (chain : Fin (n + 2) → LieSubmodule R 𝔤 M),
      StrictMono chain → False := by


  obtain ⟨E, n, hdetect, hE_bound⟩ := CategoryO.casimir_detecting_submodule hM

  exact ⟨n, CategoryO.detecting_submodule_gives_chain_bound E hdetect n hE_bound⟩

theorem CategoryO.wellFoundedGT
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    WellFoundedGT (LieSubmodule R 𝔤 M) := by
  obtain ⟨n, hn⟩ := CategoryO.finite_length hM
  rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => ?_⟩
  apply hn (fun (i : Fin (n + 2)) => f i)
  intro i j hij
  exact f.map_rel_iff.2 hij

end CategoryOResults

lemma lie_hom_commutes_uea_act
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    (f : M →ₗ⁅R, L⁆ N) (u : UniversalEnvelopingAlgebra R L) (m : M) :
    f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)) u) m) =
    ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N)) u) (f m) := by

  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u


  suffices h : ∀ m' : M,
      f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
           ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)) m') =
      ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
        ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)) (f m') from h m
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro m'
    simp only [Algebra.algebraMap_eq_smul_one]
    simp
  | ι x =>
    intro m'
    rw [show (UniversalEnvelopingAlgebra.mkAlgHom R L) ((TensorAlgebra.ι R) x) =
            (UniversalEnvelopingAlgebra.ι R) x from rfl]
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
    simp only [LieModule.toEnd_apply_apply]
    exact f.map_lie x m'
  | mul a b ha hb =>
    intro m'
    rw [map_mul, map_mul, map_mul]
    show f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
             ((UniversalEnvelopingAlgebra.mkAlgHom R L) a))
            (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
               ((UniversalEnvelopingAlgebra.mkAlgHom R L) b)) m')) =
         ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
           ((UniversalEnvelopingAlgebra.mkAlgHom R L) a))
          (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
             ((UniversalEnvelopingAlgebra.mkAlgHom R L) b)) (f m'))
    rw [ha]
    congr 1
    exact hb m'
  | add a b ha hb =>
    intro m'
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add]
    congr 1
    · exact ha m'
    · exact hb m'

theorem uea_pbw_degree_function
    (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    ∃ (v : UniversalEnvelopingAlgebra R L → WithBot ℤ),
      v 0 = ⊥ ∧
      (∀ a : UniversalEnvelopingAlgebra R L, a ≠ 0 → v a ≠ ⊥) ∧
      (∀ a b : UniversalEnvelopingAlgebra R L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b) := by sorry

theorem uea_noZeroDivisors_of_pbw
    (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    NoZeroDivisors (UniversalEnvelopingAlgebra R L) := by
  obtain ⟨v, hv0, hvne, hvmul⟩ := uea_pbw_degree_function R L
  constructor
  intro a b hab
  by_contra hc
  push_neg at hc
  obtain ⟨ha, hb⟩ := hc
  have h1 := hvmul a b ha hb
  rw [hab, hv0] at h1
  have h1' : v a + v b = ⊥ := h1.symm
  rw [WithBot.add_eq_bot] at h1'
  exact h1'.elim (hvne a ha) (hvne b hb)

theorem verma_hom_injective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {Mmu : Type*} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (wt_mu wt_lam : Δ.𝔥 →ₗ[R] R)
    (hMmu : IsVermaModule Δ Mmu wt_mu)
    (hMlam : IsVermaModule Δ Mlam wt_lam)
    (eta : Mmu →ₗ⁅R, 𝔤⁆ Mlam)
    (hne : eta ≠ 0) :
    Function.Injective eta := by


  have hker_ne_top : eta.ker ≠ ⊤ := by
    intro h
    apply hne
    ext m
    have : m ∈ eta.ker := h ▸ trivial
    exact this

  have hvmu_notin_ker : hMmu.highestWeightVec ∉ eta.ker :=
    hMmu.hwv_not_mem_proper eta.ker hker_ne_top
  have heta_vmu_ne : eta hMmu.highestWeightVec ≠ 0 := by
    intro h
    exact hvmu_notin_ker (LieModuleHom.mem_ker.mpr h)

  letI instMmu := instModuleUEASubalg Δ.𝔫_neg Mmu
  letI instMlam := instModuleUEASubalg Δ.𝔫_neg Mlam

  have hpbw_mu := pbw_verma_bijective hMmu
  have hpbw_lam := pbw_verma_bijective hMlam


  rw [← LieModuleHom.ker_eq_bot]
  rw [eq_bot_iff]
  intro m hm
  rw [LieModuleHom.mem_ker] at hm

  obtain ⟨u, rfl⟩ := hpbw_mu.2 m


  suffices hu : u = 0 by
    simp only [hu, map_zero, LieSubmodule.mem_bot]

  obtain ⟨a, ha⟩ := hpbw_lam.2 (eta hMmu.highestWeightVec)

  have ha_ne : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact heta_vmu_ne ha.symm


  have hlin : eta ((LinearMap.toSpanSingleton _ Mmu hMmu.highestWeightVec) u) =
    ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mlam)) u)
      (eta hMmu.highestWeightVec) := by

    show eta (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mmu)) u)
              hMmu.highestWeightVec) =
         ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mlam)) u)
           (eta hMmu.highestWeightVec)
    exact lie_hom_commutes_uea_act (eta.restrictLie Δ.𝔫_neg) u hMmu.highestWeightVec

  rw [hm] at hlin


  have h_mul_act : ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mlam)) u)
      (eta hMmu.highestWeightVec) =
    (LinearMap.toSpanSingleton _ Mlam hMlam.highestWeightVec) (u * a) := by
    rw [← ha]
    show ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mlam)) u)
        ((LinearMap.toSpanSingleton _ Mlam hMlam.highestWeightVec) a) =
      (LinearMap.toSpanSingleton _ Mlam hMlam.highestWeightVec) (u * a)

    show ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mlam)) u)
        (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mlam)) a)
          hMlam.highestWeightVec) =
      ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R ↥Δ.𝔫_neg Mlam)) (u * a))
        hMlam.highestWeightVec
    rw [map_mul]
    rfl

  rw [h_mul_act] at hlin

  have hua_zero : u * a = 0 := hpbw_lam.1 (hlin.symm ▸ (map_zero _).symm)

  haveI := uea_noZeroDivisors_of_pbw R ↥Δ.𝔫_neg
  exact (mul_eq_zero.mp hua_zero).resolve_right ha_ne

theorem verma_singular_one_dim
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (μ : Δ.𝔥 →ₗ[R] R)
    (v₁ v₂ : M)
    (hv₁_ne : v₁ ≠ 0)
    (hv₁_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v₁⁆ = μ h • v₁)
    (hv₁_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v₁⁆ = 0)
    (hv₂_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v₂⁆ = μ h • v₂)
    (hv₂_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v₂⁆ = 0) :
    ∃ (c : R), v₂ = c • v₁ := by

  letI : Module (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨φ, hφ⟩ := hM.free_over_nminus

  set u₁ := φ.symm v₁
  set u₂ := φ.symm v₂
  have hv₁_eq : φ u₁ = v₁ := LinearEquiv.apply_symm_apply φ v₁
  have hv₂_eq : φ u₂ = v₂ := LinearEquiv.apply_symm_apply φ v₂

  have hφu₁ : φ u₁ = (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec := by
    have key : φ u₁ = u₁ • φ (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := by
      have : u₁ = u₁ * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u₁).symm
      conv_lhs => rw [this]; exact φ.map_smul u₁ 1
    rw [key, hφ]; rfl
  have hφu₂ : φ u₂ = (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec := by
    have key : φ u₂ = u₂ • φ (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := by
      have : u₂ = u₂ * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u₂).symm
      conv_lhs => rw [this]; exact φ.map_smul u₂ 1
    rw [key, hφ]; rfl

  have hu₁_ne : (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec ≠ 0 := by
    rw [← hφu₁, hv₁_eq]; exact hv₁_ne

  have hu₁_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec⁆ =
      μ h • (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec := by
    intro h; rw [← hφu₁, hv₁_eq]; exact hv₁_wt h
  have hu₂_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec⁆ =
      μ h • (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec := by
    intro h; rw [← hφu₂, hv₂_eq]; exact hv₂_wt h

  have hu₁_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec⁆ = 0 := by
    intro e; rw [← hφu₁, hv₁_eq]; exact hv₁_npos e
  have hu₂_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec⁆ = 0 := by
    intro e; rw [← hφu₂, hv₂_eq]; exact hv₂_npos e

  obtain ⟨c, hc⟩ := pbw_nminus_singular_proportional hM μ u₁ u₂
    hu₁_ne hu₁_wt hu₁_npos hu₂_wt hu₂_npos

  refine ⟨c, ?_⟩
  rw [← hv₂_eq, ← hv₁_eq, hφu₂, hφu₁, hc]

theorem verma_hom_unique_up_to_scalar
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {Mmu : Type*} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (wt_mu wt_lam : Δ.𝔥 →ₗ[R] R)
    (hMmu : IsVermaModule Δ Mmu wt_mu)
    (hMlam : IsVermaModule Δ Mlam wt_lam)
    (eta eta' : Mmu →ₗ⁅R, 𝔤⁆ Mlam)
    (heta_ne : eta ≠ 0) :
    ∃ (c : R), ∀ m, eta' m = c • eta m := by

  have heta_vmu_ne : eta hMmu.highestWeightVec ≠ 0 := by
    intro h
    apply heta_ne
    have hker : hMmu.highestWeightVec ∈ LieModuleHom.ker eta :=
      LieModuleHom.mem_ker.mpr h
    have hspan_le : LieSubmodule.lieSpan R 𝔤 {hMmu.highestWeightVec} ≤
        LieModuleHom.ker eta :=
      LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hker)
    have hker_top : LieModuleHom.ker eta = ⊤ :=
      eq_top_iff.mpr (hMmu.generates ▸ hspan_le)
    ext m
    have hm : m ∈ LieModuleHom.ker eta := hker_top ▸ LieSubmodule.mem_top m
    simp [LieModuleHom.mem_ker.mp hm]


  obtain ⟨c, hc⟩ := verma_singular_one_dim wt_lam hMlam wt_mu
    (eta hMmu.highestWeightVec) (eta' hMmu.highestWeightVec)
    heta_vmu_ne
    (fun h => by rw [← LieModuleHom.map_lie]; rw [hMmu.cartan_action]; simp [map_smul])
    (fun e => by rw [← LieModuleHom.map_lie]; rw [hMmu.npos_action]; simp)
    (fun h => by rw [← LieModuleHom.map_lie]; rw [hMmu.cartan_action]; simp [map_smul])
    (fun e => by rw [← LieModuleHom.map_lie]; rw [hMmu.npos_action]; simp)

  have hval : (eta' - c • eta) hMmu.highestWeightVec = 0 := by
    simp [LieModuleHom.sub_apply, LieModuleHom.smul_apply, hc, sub_self]


  have hker_top : LieModuleHom.ker (eta' - c • eta) = ⊤ := by
    have hker : hMmu.highestWeightVec ∈ LieModuleHom.ker (eta' - c • eta) :=
      LieModuleHom.mem_ker.mpr hval
    have hspan_le : LieSubmodule.lieSpan R 𝔤 {hMmu.highestWeightVec} ≤
        LieModuleHom.ker (eta' - c • eta) := by
      apply LieSubmodule.lieSpan_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact hker
    exact eq_top_iff.mpr (hMmu.generates ▸ hspan_le)

  exact ⟨c, fun m => by
    have hm : m ∈ LieModuleHom.ker (eta' - c • eta) := hker_top ▸ LieSubmodule.mem_top m
    rw [LieModuleHom.mem_ker] at hm

    have : (eta' - c • eta) m = 0 := hm
    rwa [LieModuleHom.sub_apply, LieModuleHom.smul_apply, sub_eq_zero] at this⟩

universe u_vm in
theorem IsVermaModule.universal_map'
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type u_vm} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    {V : Type u_vm} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (v : V)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v)
    (hv_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) :
    ∃ (η : M →ₗ⁅R, 𝔤⁆ V), η hM.highestWeightVec = v :=
  hM.universal_map V v hv_wt hv_npos

universe u_vhsw in
theorem verma_hom_same_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {Mmu : Type u_vhsw} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    {Mlam : Type u_vhsw} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hMmu : IsVermaModule Δ Mmu wt)
    (hMlam : IsVermaModule Δ Mlam wt) :
    ∃ (eta : Mmu →ₗ⁅R, 𝔤⁆ Mlam), eta ≠ 0 := by


  obtain ⟨η, hη⟩ := hMmu.universal_map' hMlam.highestWeightVec
    hMlam.cartan_action hMlam.npos_action

  exact ⟨η, fun h => hMlam.hwv_ne_zero (by rw [← hη]; simp [h])⟩

theorem exercise_8_15_weight_space_has_singular
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (α : Δ.𝔥 →ₗ[R] R)
    (hα : α ∈ rd.posRoots)
    (n : ℕ) (hn : 0 < n)
    (hcoroot : rd.corootPairing (wt + wg.ρ) α = (n : R)) :
    ∃ (v : Δ.weightSubspace M (wt - n • α)),
      (v : M) ≠ 0 ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), (v : M)⁆ = 0) := by sorry

theorem exercise_8_15_singular_vector
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (α : Δ.𝔥 →ₗ[R] R)
    (hα : α ∈ rd.posRoots)
    (n : ℕ) (hn : 0 < n)
    (hcoroot : rd.corootPairing (wt + wg.ρ) α = (n : R)) :
    ∃ (v : M), v ≠ 0 ∧
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = (wt - n • α) h • v) ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by
  obtain ⟨⟨v, hv_mem⟩, hv_ne, hv_killed⟩ :=
    exercise_8_15_weight_space_has_singular wt hM α hα n hn hcoroot
  exact ⟨v, hv_ne, fun h => hv_mem h, hv_killed⟩

theorem shapovalov_singular_vector_step
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hstep : ∃ α, ReflectionLT rd α mu lam)
    (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ)) :
    ∃ (v : Mlam), v ≠ 0 ∧
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = (mu - wg.ρ) h • v) ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by

  obtain ⟨α, hα_pos, n, hn_pos, hcoroot, hmu_eq⟩ := hstep


  have hcoroot' : rd.corootPairing ((lam - wg.ρ) + wg.ρ) α = (n : R) := by
    have : (lam - wg.ρ) + wg.ρ = lam := by abel
    rw [this]; exact hcoroot
  obtain ⟨v, hv_ne, hv_wt, hv_killed⟩ :=
    exercise_8_15_singular_vector (lam - wg.ρ) hMlam α hα_pos n hn_pos hcoroot'


  refine ⟨v, hv_ne, ?_, hv_killed⟩
  intro h
  rw [hv_wt h]
  congr 1


  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [hmu_eq]
  simp [LinearMap.sub_apply, LinearMap.smul_apply]
  ring

universe u_vhss in

theorem verma_hom_single_step
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mmu : Type u_vhss} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    {Mlam : Type u_vhss} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hstep : ∃ α, ReflectionLT rd α mu lam)
    (hMmu : IsVermaModule Δ Mmu (mu - wg.ρ))
    (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ)) :
    ∃ (eta : Mmu →ₗ⁅R, 𝔤⁆ Mlam), eta ≠ 0 := by


  obtain ⟨v, hv_ne, hv_wt, hv_killed⟩ :=
    shapovalov_singular_vector_step mu lam hstep hMlam

  obtain ⟨Mmu', instACG', instMod', instLRM', instLM', ⟨hMmu'⟩⟩ :=
    verma_module_exists (R := R) (𝔤 := 𝔤) Δ (mu - wg.ρ)


  obtain ⟨η, hη_val⟩ := hMmu'.universal_map Mlam v hv_wt hv_killed

  have hη_ne : η ≠ 0 := by
    intro h_eq
    have : η hMmu'.highestWeightVec = 0 := by rw [h_eq]; simp
    rw [hη_val] at this
    exact hv_ne this

  obtain ⟨f, hf_ne⟩ := verma_hom_same_weight (mu - wg.ρ) hMmu hMmu'

  refine ⟨η.comp f, ?_⟩
  intro h_eq

  have hη_inj := verma_hom_injective (mu - wg.ρ) (lam - wg.ρ) hMmu' hMlam η hη_ne

  have : f = 0 := by
    ext x
    have hx := LieModuleHom.congr_fun h_eq x
    simp [LieModuleHom.comp_apply] at hx
    have hx' : η (f x) = η 0 := by rw [hx, map_zero]
    exact hη_inj hx'
  exact hf_ne this

universe u_vhe in

theorem verma_hom_exists
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mmu : Type u_vhe} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    {Mlam : Type u_vhe} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hle : BruhatLE rd mu lam)
    (hMmu : IsVermaModule Δ Mmu (mu - wg.ρ))
    (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ)) :
    ∃ (eta : Mmu →ₗ⁅R, 𝔤⁆ Mlam), eta ≠ 0 := by

  revert Mlam
  induction hle with
  | refl =>

    intro Mlam _ _ _ _ hMlam
    exact verma_hom_same_weight _ hMmu hMlam
  | tail hab hbc ih =>

    rename_i b c
    intro Mlam instACG instMod instLRM instLM hMlam

    obtain ⟨Mmid, instACG', instMod', instLRM', instLM', ⟨hMmid⟩⟩ :=
      verma_module_exists (R := R) (𝔤 := 𝔤) Δ (b - wg.ρ)

    obtain ⟨f, hf⟩ := @ih Mmid instACG' instMod' instLRM' instLM' hMmid

    obtain ⟨g, hg⟩ := verma_hom_single_step b c hbc hMmid hMlam

    refine ⟨g.comp f, ?_⟩
    intro h_eq
    have hg_inj := verma_hom_injective (b - wg.ρ) (c - wg.ρ) hMmid hMlam g hg
    have : f = 0 := by
      ext x
      have hx := LieModuleHom.congr_fun h_eq x
      simp [LieModuleHom.comp_apply] at hx
      have hx' : g (f x) = g 0 := by rw [hx, map_zero]
      exact hg_inj hx'
    exact hf this

universe u_vt in

theorem verma_theorem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mmu : Type u_vt} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    {Mlam : Type u_vt} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hle : BruhatLE rd mu lam)
    (hMmu : IsVermaModule Δ Mmu (mu - wg.ρ))
    (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ)) :
    ∃ (eta : Mmu →ₗ⁅R, 𝔤⁆ Mlam), eta ≠ 0 ∧ Function.Injective eta ∧
      (∀ (eta' : Mmu →ₗ⁅R, 𝔤⁆ Mlam), ∃ (c : R), ∀ m, eta' m = c • eta m) := by

  obtain ⟨eta, heta_ne⟩ := verma_hom_exists mu lam hle hMmu hMlam
  exact ⟨eta, heta_ne,

    verma_hom_injective (mu - wg.ρ) (lam - wg.ρ) hMmu hMlam eta heta_ne,


    fun eta' => verma_hom_unique_up_to_scalar (mu - wg.ρ) (lam - wg.ρ) hMmu hMlam eta eta' heta_ne⟩

theorem verma_composition_factor
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hle : BruhatLE rd mu lam)
    (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ)) :
    ∃ (N N' : LieSubmodule R 𝔤 Mlam), N' < N ∧
      Nonempty (IsHighestWeightModule Δ (↥N ⧸ (N'.comap N.incl)) (mu - wg.ρ)) := by


  obtain ⟨Mmu, instACG, instMod, instLRM, instLM, ⟨hMmu⟩⟩ :=
    verma_module_exists (R := R) (𝔤 := 𝔤) Δ (mu - wg.ρ)

  obtain ⟨η, hη_ne⟩ := @verma_hom_exists _ _ _ _ _ _ _ _ _ instACG instMod instLRM instLM
    _ _ _ _ _ mu lam hle hMmu hMlam

  have hη_inj : Function.Injective η :=
    verma_hom_injective (mu - wg.ρ) (lam - wg.ρ) hMmu hMlam η hη_ne

  set N := η.range with hN_def

  obtain ⟨J, hJ_ne_top, hJ_max⟩ := hMmu.exists_unique_maximal_submodule

  set N'_in_Mlam := LieSubmodule.map η J with hN'_def

  have hN'_le_N : N'_in_Mlam ≤ N := LieSubmodule.map_le_range (f := η)
  have hN'_ne_N : N'_in_Mlam ≠ N := by
    intro h
    apply hJ_ne_top
    rw [eq_top_iff]
    intro m _
    have hηm : η m ∈ N := (η.mem_range (η m)).mpr ⟨m, rfl⟩
    rw [← h] at hηm
    obtain ⟨j, hj, hηeq⟩ := (LieSubmodule.mem_map (η m)).mp hηm
    exact hη_inj hηeq ▸ hj
  have hN'_lt_N : N'_in_Mlam < N := lt_of_le_of_ne hN'_le_N hN'_ne_N

  refine ⟨N, N'_in_Mlam, hN'_lt_N, ?_⟩
  set N'_rel := N'_in_Mlam.comap N.incl with hN'_rel_def

  have hη_range : ∀ m : Mmu, η m ∈ N := fun m => (η.mem_range (η m)).mpr ⟨m, rfl⟩
  let η_N : Mmu →ₗ⁅R, 𝔤⁆ ↥N :=
    { toFun := fun m => ⟨η m, hη_range m⟩
      map_add' := fun x y => by simp [map_add]
      map_smul' := fun r x => by simp [map_smul]
      map_lie' := fun {x m} => by simp [Subtype.ext_iff, LieModuleHom.map_lie] }
  let φ : Mmu →ₗ⁅R, 𝔤⁆ (↥N ⧸ N'_rel) := (LieSubmodule.Quotient.mk' N'_rel).comp η_N
  have hφ_surj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N'_rel q
    obtain ⟨m, rfl⟩ := (η.mem_range y).mp hy
    exact ⟨m, rfl⟩

  have hφ_ker_eq_J : ∀ m : Mmu, φ m = 0 ↔ m ∈ J := by
    intro m
    constructor
    · intro hφm
      change (LieSubmodule.Quotient.mk' N'_rel) (η_N m) = 0 at hφm
      rw [LieSubmodule.Quotient.mk_eq_zero] at hφm
      rw [hN'_rel_def] at hφm
      simp only [LieSubmodule.mem_comap, LieSubmodule.incl_apply] at hφm
      obtain ⟨j, hj, hηeq⟩ := (LieSubmodule.mem_map (η m)).mp hφm
      exact hη_inj hηeq ▸ hj
    · intro hm
      change (LieSubmodule.Quotient.mk' N'_rel) (η_N m) = 0
      rw [LieSubmodule.Quotient.mk_eq_zero]
      rw [hN'_rel_def]
      simp only [LieSubmodule.mem_comap, LieSubmodule.incl_apply]
      exact (LieSubmodule.mem_map (η m)).mpr ⟨m, hm, rfl⟩

  set v_quot := φ hMmu.highestWeightVec with hv_quot_def

  have hwv_ne : v_quot ≠ 0 := by
    intro hv_zero
    rw [hv_quot_def] at hv_zero
    have hv_in_J := (hφ_ker_eq_J _).mp hv_zero
    apply hJ_ne_top
    rw [eq_top_iff, ← hMmu.generates]
    exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_J)

  have hcartan : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v_quot⁆ = (mu - wg.ρ) h • v_quot := by
    intro h


    have h1 : ⁅(h : 𝔤), v_quot⁆ = φ ⁅(h : 𝔤), hMmu.highestWeightVec⁆ := by
      rw [hv_quot_def, ← φ.map_lie]
    rw [h1, hMmu.cartan_action h, map_smul, ← hv_quot_def]

  have hnpos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v_quot⁆ = 0 := by
    intro e
    have h1 : ⁅(e : 𝔤), v_quot⁆ = φ ⁅(e : 𝔤), hMmu.highestWeightVec⁆ := by
      rw [hv_quot_def, ← φ.map_lie]
    rw [h1, hMmu.npos_action e, map_zero]

  have hgen : LieSubmodule.lieSpan R 𝔤 {v_quot} = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨m, rfl⟩ := hφ_surj q
    suffices m ∈ LieSubmodule.comap φ (LieSubmodule.lieSpan R 𝔤 {v_quot}) by
      exact LieSubmodule.mem_comap.mp this
    have hcomap_top : LieSubmodule.comap φ (LieSubmodule.lieSpan R 𝔤 {v_quot}) = ⊤ := by
      rw [eq_top_iff, ← hMmu.generates]
      apply LieSubmodule.lieSpan_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact LieSubmodule.mem_comap.mpr (LieSubmodule.subset_lieSpan (Set.mem_singleton _))
    rw [hcomap_top]
    trivial
  exact ⟨⟨v_quot, hwv_ne, hcartan, hnpos, hgen⟩⟩

lemma IsInQPlus_antisymm_catO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hpos : rd.IsInQPlus μ)
    (hneg : rd.IsInQPlus (-μ)) :
    μ = 0 := by
  classical
  obtain ⟨c, hc⟩ := hpos

  obtain ⟨d, hd⟩ := hneg
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hμ (by rw [hc]; exact Finset.sum_eq_zero fun β hβ => by simp [hall β hβ])
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _; rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [Finset.ne_of_mem_erase hγ]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ; omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

theorem CategoryO.exists_maximal_weight_vector
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) [Nontrivial M] :
    ∃ (v : M) (μ : Δ.𝔥 →ₗ[R] R),
      v ≠ 0 ∧
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v) ∧
      (∀ (ν : Δ.𝔥 →ₗ[R] R) (w : M),
        (∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = ν h • w) →
        rd.IsInQPlus (ν - μ) → ν ≠ μ → w = 0) := by
  classical

  obtain ⟨m, hm_ne⟩ := exists_ne (0 : M)

  obtain ⟨S, wv, hm_decomp⟩ := hM.weight_decomp m

  have hS_ne : ∃ μ₀ ∈ S, (wv μ₀ : M) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hm_ne
    rw [hm_decomp]
    exact Finset.sum_eq_zero fun μ hμ => hall μ hμ
  obtain ⟨μ₀, hμ₀_mem, hv₀_ne⟩ := hS_ne

  have hμ₀_wt : μ₀ ∈ weights Δ M := by
    rw [weights, Set.mem_setOf_eq]
    intro h
    apply hv₀_ne
    rw [Submodule.eq_bot_iff] at h
    exact h _ (wv μ₀).prop

  obtain ⟨bds, hbds⟩ := hM.weight_bound


  have hcontain : ∀ μ ∈ weights Δ M,
      ∃ wt ∈ bds, rd.IsInQPlus (wt - μ) := hbds


  let T_map : (Δ.𝔥 →ₗ[R] R) → Finset (Δ.𝔥 →ₗ[R] R) :=
    fun wt => (rd.cone_inter_finite wt wt).choose
  have hT_map_spec : ∀ wt, ∀ γ,
      (∃ c : _ → ℕ, wt - γ = ∑ α ∈ rd.posRoots, (c α) • α) →
      (∃ c : _ → ℕ, wt - γ = ∑ α ∈ rd.posRoots, (c α) • α) →
      γ ∈ T_map wt :=
    fun wt => (rd.cone_inter_finite wt wt).choose_spec

  let T : Finset (Δ.𝔥 →ₗ[R] R) := bds.biUnion (fun wt => T_map wt)

  have hweights_in_T : ∀ μ ∈ weights Δ M, μ ∈ T := by
    intro μ hμ
    obtain ⟨wt, hwt_mem, hwt_bound⟩ := hcontain μ hμ
    obtain ⟨c, hc⟩ := hwt_bound
    have hγ_in : μ ∈ T_map wt := by
      exact hT_map_spec wt μ ⟨c, hc⟩ ⟨c, hc⟩

    exact Finset.mem_biUnion.mpr ⟨wt, hwt_mem, hγ_in⟩

  let T_wt : Finset (Δ.𝔥 →ₗ[R] R) := T.filter (fun μ => μ ∈ weights Δ M)

  have hT_wt_ne : T_wt.Nonempty := by
    exact ⟨μ₀, Finset.mem_filter.mpr ⟨hweights_in_T μ₀ hμ₀_wt, hμ₀_wt⟩⟩


  letI : LE (Δ.𝔥 →ₗ[R] R) := ⟨fun μ ν => rd.IsInQPlus (ν - μ)⟩

  letI : IsTrans (Δ.𝔥 →ₗ[R] R) LE.le := ⟨by
    intro μ ν ξ hμν hνξ
    show rd.IsInQPlus (ξ - μ)
    exact rd.IsInQPlus_trans ξ ν μ hνξ hμν⟩

  obtain ⟨μ, hμ_mem, hμ_max⟩ := Finset.exists_maximal hT_wt_ne

  rw [Finset.mem_filter] at hμ_mem
  have hμ_wt : μ ∈ weights Δ M := hμ_mem.2

  rw [weights, Set.mem_setOf_eq] at hμ_wt
  rw [Submodule.ne_bot_iff] at hμ_wt
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ_wt

  have hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v := hv_mem

  refine ⟨v, μ, hv_ne, hv_wt, ?_⟩
  intro ν w hw_wt hν_above hν_ne

  by_contra hw_ne
  push_neg at hw_ne

  have hν_wt : ν ∈ weights Δ M := by
    rw [weights, Set.mem_setOf_eq]
    intro h
    apply hw_ne
    rw [Submodule.eq_bot_iff] at h
    exact h _ hw_wt

  have hν_in_T : ν ∈ T := hweights_in_T ν hν_wt

  have hν_in_T_wt : ν ∈ T_wt := Finset.mem_filter.mpr ⟨hν_in_T, hν_wt⟩

  have hμ_le_ν : (μ : Δ.𝔥 →ₗ[R] R) ≤ ν := hν_above
  have hν_le_μ : (ν : Δ.𝔥 →ₗ[R] R) ≤ μ := hμ_max hν_in_T_wt hμ_le_ν

  have hνμ_zero : ν - μ = 0 := by
    exact IsInQPlus_antisymm_catO rd (ν - μ) hν_above (by rwa [neg_sub])

  have : ν = μ := sub_eq_zero.mp hνμ_zero
  exact hν_ne this

lemma root_vec_raises_weight_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
    (μ : Δ.𝔥 →ₗ[R] R) (w : M)
    (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) :
    ∀ (h : Δ.𝔥), ⁅(h : 𝔤), (⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ : M)⁆ =
      (α + μ) h • ⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ := by
  intro h
  have hleibniz := leibniz_lie (h : 𝔤) (↑(rd.posRootVec α hα) : 𝔤) w
  have hroot := rd.posRootVec_weight α hα h
  have hwt := hw_wt h
  rw [hroot, hwt] at hleibniz
  rw [smul_lie, LieModule.lie_smul] at hleibniz
  rw [hleibniz]
  simp only [LinearMap.add_apply]
  rw [← add_smul]

theorem CategoryO.exists_singular_vector
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) [Nontrivial M] :
    ∃ (v : M) (lam : Δ.𝔥 →ₗ[R] R),
      v ≠ 0 ∧
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = lam h • v) ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by
  classical

  obtain ⟨v, μ, hv_ne, hv_wt, hμ_max⟩ := CategoryO.exists_maximal_weight_vector hM
  refine ⟨v, μ, hv_ne, hv_wt, ?_⟩

  intro e

  obtain ⟨c, hc⟩ := rd.npos_span e

  have hew : (⁅(e : 𝔤), v⁆ : M) =
      ∑ x ∈ rd.posRoots.attach, c x.1 x.2 • ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), v⁆ := by
    conv_lhs => rw [show (e : 𝔤) = ∑ x ∈ rd.posRoots.attach,
      c x.1 x.2 • (↑(rd.posRootVec x.1 x.2) : 𝔤) from hc]
    rw [sum_lie]
    congr 1
    ext x
    rw [smul_lie]

  have hzero : ∀ (x : { x // x ∈ rd.posRoots }),
      ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), v⁆ = (0 : M) := by
    intro ⟨α, hα⟩
    apply hμ_max (α + μ)
    · exact root_vec_raises_weight_local α hα μ v hv_wt
    · show rd.IsInQPlus (α + μ - μ)
      rw [add_sub_cancel_right]
      exact ⟨fun β => if β = α then 1 else 0, by simp [Finset.sum_ite_eq', hα]⟩
    · intro heq
      apply rd.posRoots_ne_zero α hα
      have : α + μ - μ = μ - μ := by rw [heq]
      simp [add_sub_cancel_right, sub_self] at this
      exact this
  rw [hew]
  simp only [hzero, smul_zero, Finset.sum_const_zero]

theorem CategoryO.simple_objects_are_highest_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (hirr : LieModule.IsIrreducible R 𝔤 M) :
    ∃ (lam : Δ.𝔥 →ₗ[R] R),
      Nonempty (IsHighestWeightModule Δ M lam) := by


  haveI : LieModule.IsIrreducible R 𝔤 M := hirr
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible R 𝔤 M
  obtain ⟨v, lam, hv_ne, hv_weight, hv_killed⟩ :=
    CategoryO.exists_singular_vector hM (M := M)

  have hgen : LieSubmodule.lieSpan R 𝔤 {v} = ⊤ := by
    have hspan_ne_bot : LieSubmodule.lieSpan R 𝔤 {v} ≠ ⊥ := by
      intro h
      have := (LieSubmodule.lieSpan_eq_bot_iff R 𝔤 M).mp h v (Set.mem_singleton v)
      exact hv_ne this
    exact (hirr.eq_bot_or_eq_top _).resolve_left hspan_ne_bot

  exact ⟨lam, ⟨{
    highestWeightVec := v
    hwv_ne_zero := hv_ne
    cartan_action := hv_weight
    npos_action := hv_killed
    generates := hgen
  }⟩⟩

def WeylStabilizerModQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w : wg.W | ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    wg.dualAction w x - x = ∑ α ∈ rd.posRoots, c α • α}

def WeylStabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w : wg.W | wg.dualAction w x = x}

lemma WeylStabilizer_mul_closed
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R)
    {w₁ w₂ : wg.W}
    (h₁ : w₁ ∈ WeylStabilizer rd wg x)
    (h₂ : w₂ ∈ WeylStabilizer rd wg x) :
    w₁ * w₂ ∈ WeylStabilizer rd wg x := by
  show wg.dualAction (w₁ * w₂) x = x
  rw [wg.dualAction_mul, h₂, h₁]

structure RootSystemWithReflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  allRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_sub : ∀ α ∈ rd.posRoots, α ∈ allRoots
  roots_pos_or_neg : ∀ α ∈ allRoots, α ∈ rd.posRoots ∨ -α ∈ rd.posRoots
  reflection : (Δ.𝔥 →ₗ[R] R) → wg.W
  coroot : (Δ.𝔥 →ₗ[R] R) → Δ.𝔥
  corootPairing_eq_eval : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    rd.corootPairing μ α = μ (coroot α)
  reflection_formula : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    wg.dualAction (reflection α) μ = μ - (μ (coroot α)) • α
  reflection_order_two : ∀ α ∈ allRoots, reflection α * reflection α = 1
  allRoots_neg_closed : ∀ α ∈ allRoots, -α ∈ allRoots
  reflection_neg : ∀ α ∈ allRoots, reflection (-α) = reflection α
  reflection_conjugation : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    reflection α * reflection β * reflection α =
    reflection (wg.dualAction (reflection α) β)
  allRoots_reflection_closed : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    wg.dualAction (reflection α) β ∈ allRoots
  dualAction_sub : ∀ (w : wg.W) (μ ν : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (μ - ν) = wg.dualAction w μ - wg.dualAction w ν
  dualAction_zsmul : ∀ (w : wg.W) (n : ℤ) (μ : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (n • μ) = n • wg.dualAction w μ
  dualAction_rootLattice : ∀ (w : wg.W) (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    ∃ (c' : (Δ.𝔥 →ₗ[R] R) → ℤ),
      wg.dualAction w (∑ α ∈ rd.posRoots, c α • α) = ∑ α ∈ rd.posRoots, c' α • α
  pairing_integral : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ allRoots →
    ∀ (μ : Δ.𝔥 →ₗ[R] R),
    (∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
      -(μ (coroot α)) • α = ∑ γ ∈ rd.posRoots, c γ • γ) →
    ∃ (n : ℤ), μ (coroot α) = (n : R)
  generated_by_reflections : ∀ w : wg.W, ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
    (∀ i, αs i ∈ allRoots) ∧
    w = (List.ofFn (fun i => reflection (αs i))).prod
  ρ_eq_half_sum : (2 : R) • wg.ρ = rd.sumPosRoots

theorem RootSystemWithReflections.stabilizer_gen_by_reflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg x) :
    ∃ (m : ℕ) (βs : Fin m → Δ.𝔥 →ₗ[R] R),
      (∀ i, βs i ∈ rs.allRoots ∧ rs.reflection (βs i) ∈ WeylStabilizerModQ rd wg x) ∧
      w = (List.ofFn (fun i => rs.reflection (βs i))).prod := by sorry

theorem RootSystemWithReflections.dualAction_mul
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (_rs : RootSystemWithReflections rd wg)
    (w₁ w₂ : wg.W) (μ : Δ.𝔥 →ₗ[R] R) :
    wg.dualAction (w₁ * w₂) μ = wg.dualAction w₁ (wg.dualAction w₂ μ) :=
  wg.dualAction_mul w₁ w₂ μ

def rootsOfStabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) : Set (Δ.𝔥 →ₗ[R] R) :=
  {α | α ∈ rs.allRoots ∧ rs.reflection α ∈ WeylStabilizerModQ rd wg x}

def IsRootSubsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=

  (∀ α ∈ S, α ∈ rs.allRoots) ∧

  ((0 : Δ.𝔥 →ₗ[R] R) ∉ S) ∧

  (∀ α ∈ S, -α ∈ S) ∧

  (∀ α ∈ S, ∀ β ∈ S, wg.dualAction (rs.reflection α) β ∈ S)

def corootsOf
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Set Δ.𝔥 :=
  {h : Δ.𝔥 | ∃ α ∈ S, h = rs.coroot α}

lemma WeylStabilizerModQ_mul_closed
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R)
    {w₁ w₂ : wg.W}
    (h₁ : w₁ ∈ WeylStabilizerModQ rd wg x)
    (h₂ : w₂ ∈ WeylStabilizerModQ rd wg x) :
    w₁ * w₂ ∈ WeylStabilizerModQ rd wg x := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c₂', hc₂'⟩ := rs.dualAction_rootLattice w₁ c₂
  refine ⟨fun α => c₁ α + c₂' α, ?_⟩


  have hmul := rs.dualAction_mul w₁ w₂ x
  have hsub := rs.dualAction_sub w₁ (wg.dualAction w₂ x) x

  have hkey : wg.dualAction w₁ (wg.dualAction w₂ x - x) =
    wg.dualAction w₁ (wg.dualAction w₂ x) - wg.dualAction w₁ x := hsub

  rw [hc₂] at hkey

  rw [hc₂'] at hkey


  have : wg.dualAction (w₁ * w₂) x - x =
    (wg.dualAction w₁ (wg.dualAction w₂ x) - wg.dualAction w₁ x) +
    (wg.dualAction w₁ x - x) := by
    rw [hmul]
    abel
  rw [this, ← hkey, hc₁, ← Finset.sum_add_distrib]
  congr 1
  funext α
  show c₂' α • α + c₁ α • α = (c₁ α + c₂' α) • α
  rw [add_comm (c₁ α) (c₂' α), add_zsmul]

theorem weyl_generated_by_root_reflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg) :
    ∀ w : wg.W, ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
      (∀ i, αs i ∈ rs.allRoots) ∧
      w = (List.ofFn (fun i => rs.reflection (αs i))).prod :=
  fun w => rs.generated_by_reflections w

lemma cst_stabilizer_generation_aux
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    ∀ n, ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg x →
    ∀ (αs : Fin n → Δ.𝔥 →ₗ[R] R),
      (∀ i, αs i ∈ rs.allRoots) →
      w = (List.ofFn (fun i => rs.reflection (αs i))).prod →
    ∃ (m : ℕ) (βs : Fin m → Δ.𝔥 →ₗ[R] R),
      (∀ i, βs i ∈ rs.allRoots ∧ rs.reflection (βs i) ∈ WeylStabilizerModQ rd wg x) ∧
      w = (List.ofFn (fun i => rs.reflection (βs i))).prod := by
  intro _n w hw _αs _hαs_roots _hw_eq
  exact rs.stabilizer_gen_by_reflections x w hw

theorem cst_stabilizer_generation
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R)
    (w : wg.W) (hw : w ∈ WeylStabilizerModQ rd wg x) :
    ∃ (m : ℕ) (βs : Fin m → Δ.𝔥 →ₗ[R] R),
      (∀ i, βs i ∈ rs.allRoots ∧ rs.reflection (βs i) ∈ WeylStabilizerModQ rd wg x) ∧
      w = (List.ofFn (fun i => rs.reflection (βs i))).prod := by

  obtain ⟨n, αs, hαs_roots, hw_eq⟩ := rs.generated_by_reflections w

  exact cst_stabilizer_generation_aux rd wg rs x n w hw αs hαs_roots hw_eq

theorem cst_stabilizer_refine
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    ∀ w ∈ WeylStabilizerModQ rd wg x,
    ∀ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
      (∀ i, αs i ∈ rs.allRoots) →
      w = (List.ofFn (fun i => rs.reflection (αs i))).prod →
      ∃ (m : ℕ) (βs : Fin m → Δ.𝔥 →ₗ[R] R),
        (∀ i, βs i ∈ rs.allRoots ∧ rs.reflection (βs i) ∈ WeylStabilizerModQ rd wg x) ∧
        w = (List.ofFn (fun i => rs.reflection (βs i))).prod := by

  intro w hw _n _αs _hαs _hw_eq
  exact cst_stabilizer_generation rd wg rs x w hw

theorem chevalley_shephard_todd_raw
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    ∀ w ∈ WeylStabilizerModQ rd wg x,
      ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
        (∀ i, αs i ∈ rs.allRoots ∧ rs.reflection (αs i) ∈ WeylStabilizerModQ rd wg x) ∧
        w = (List.ofFn (fun i => rs.reflection (αs i))).prod := by
  intro w hw

  obtain ⟨n, αs, hαs_roots, hw_eq⟩ := weyl_generated_by_root_reflections rd wg rs w

  exact cst_stabilizer_refine rd wg rs x w hw n αs hαs_roots hw_eq

theorem chevalley_shephard_todd_stabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    ∀ w ∈ WeylStabilizerModQ rd wg x,
      ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
        (∀ i, αs i ∈ rootsOfStabilizer rd wg rs x) ∧
        w = (List.ofFn (fun i => rs.reflection (αs i))).prod := by
  intro w hw
  obtain ⟨n, αs, hαs, hw_eq⟩ := chevalley_shephard_todd_raw rd wg rs x w hw
  exact ⟨n, αs, fun i => ⟨(hαs i).1, (hαs i).2⟩, hw_eq⟩

theorem Wx_generated_by_reflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    ∀ w ∈ WeylStabilizerModQ rd wg x,
      ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
        (∀ i, αs i ∈ rootsOfStabilizer rd wg rs x) ∧
        w = (List.ofFn (fun i => rs.reflection (αs i))).prod :=
  chevalley_shephard_todd_stabilizer rd wg rs x

theorem Wx_roots_form_root_system
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    IsRootSubsystem rd wg rs (rootsOfStabilizer rd wg rs x) := by


  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro α hα
    exact hα.1
  ·

    intro h0
    have h0_in : (0 : Δ.𝔥 →ₗ[R] R) ∈ rs.allRoots := h0.1
    rcases rs.roots_pos_or_neg 0 h0_in with hp | hn
    · exact absurd rfl (rd.posRoots_ne_zero 0 hp)
    · simp at hn
      exact absurd rfl (rd.posRoots_ne_zero 0 hn)
  ·


    intro α hα
    refine ⟨rs.allRoots_neg_closed α hα.1, ?_⟩
    rw [rs.reflection_neg α hα.1]
    exact hα.2
  ·


    intro α hα β hβ

    have h_root : wg.dualAction (rs.reflection α) β ∈ rs.allRoots :=
      rs.allRoots_reflection_closed α hα.1 β hβ.1
    refine ⟨h_root, ?_⟩


    rw [← rs.reflection_conjugation α hα.1 β hβ.1]
    exact WeylStabilizerModQ_mul_closed rd wg rs x
      (WeylStabilizerModQ_mul_closed rd wg rs x hα.2 hβ.2)
      hα.2

theorem Wx_is_weyl_group_of_Rx
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :


    (∀ w ∈ WeylStabilizerModQ rd wg x,
      ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
        (∀ i, αs i ∈ rootsOfStabilizer rd wg rs x) ∧
        w = (List.ofFn (fun i => rs.reflection (αs i))).prod) ∧
    (∀ α, α ∈ rootsOfStabilizer rd wg rs x → rs.reflection α ∈ WeylStabilizerModQ rd wg x) := by
  constructor
  ·

    exact Wx_generated_by_reflections rd wg rs x
  ·
    intro α hα
    exact hα.2

theorem Rx_dual_is_root_subsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :


    ∀ h : Δ.𝔥,
      h ∈ corootsOf rs (rootsOfStabilizer rd wg rs x) ↔
        (h ∈ Submodule.span ℤ (corootsOf rs (rootsOfStabilizer rd wg rs x)) ∧
         h ∈ corootsOf rs (↑rs.allRoots : Set (Δ.𝔥 →ₗ[R] R))) := by
  intro h
  constructor
  ·


    intro hh
    constructor
    · exact Submodule.subset_span hh
    · obtain ⟨α, hα_mem, hα_eq⟩ := hh
      refine ⟨α, ?_, hα_eq⟩
      simp only [Finset.mem_coe]
      exact hα_mem.1
  ·


    intro ⟨h_span, h_all⟩

    obtain ⟨β, hβ_all, hβ_eq⟩ := h_all
    simp only [Finset.mem_coe] at hβ_all

    refine ⟨β, ⟨hβ_all, ?_⟩, hβ_eq⟩


    have h_int_stab : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ rootsOfStabilizer rd wg rs x →
        ∃ (n : ℤ), x (rs.coroot α) = (n : R) := by
      intro α hα
      apply rs.pairing_integral α hα.1 x

      obtain ⟨c, hc⟩ := hα.2

      have hrefl := rs.reflection_formula α hα.1 x


      have : wg.dualAction (rs.reflection α) x - x = -(x (rs.coroot α)) • α := by
        rw [hrefl]
        simp [sub_sub_cancel_left]
      rw [← this]
      exact ⟨c, hc⟩


    have h_int_beta : ∃ (N : ℤ), x (rs.coroot β) = (N : R) := by

      let S : Submodule ℤ Δ.𝔥 :=
        { carrier := {v : Δ.𝔥 | ∃ (n : ℤ), x v = (n : R)}
          add_mem' := by
            intro a b ⟨na, ha⟩ ⟨nb, hb⟩
            exact ⟨na + nb, by rw [map_add, ha, hb, Int.cast_add]⟩
          zero_mem' := ⟨0, by simp⟩
          smul_mem' := by
            intro m v ⟨n, hn⟩
            refine ⟨m * n, ?_⟩
            show x ((m : ℤ) • v) = ((m * n : ℤ) : R)
            rw [← Int.cast_smul_eq_zsmul R m v, map_smul, hn, Int.cast_mul, smul_eq_mul] }

      have h_sub : corootsOf rs (rootsOfStabilizer rd wg rs x) ⊆ S := by
        intro v hv
        obtain ⟨α, hα_mem, hα_eq⟩ := hv
        rw [hα_eq]
        exact h_int_stab α hα_mem

      rw [hβ_eq] at h_span

      exact Submodule.span_le.mpr h_sub h_span


    obtain ⟨N, hN⟩ := h_int_beta
    show rs.reflection β ∈ WeylStabilizerModQ rd wg x

    rw [WeylStabilizerModQ]
    simp only [Set.mem_setOf_eq]

    have hreflβ := rs.reflection_formula β hβ_all x

    have hdiff : wg.dualAction (rs.reflection β) x - x = -(x (rs.coroot β)) • β := by
      rw [hreflβ]
      simp [sub_sub_cancel_left]
    rw [hdiff, hN]


    have h_zsmul : -((N : R)) • β = (-N : ℤ) • β := by
      rw [← Int.cast_neg, Int.cast_smul_eq_zsmul R]
    rw [h_zsmul]
    rcases rs.roots_pos_or_neg β hβ_all with h_pos | h_neg
    ·
      classical
      refine ⟨fun γ => if γ = β then -N else 0, ?_⟩
      rw [Finset.sum_eq_single β
        (fun γ _ hγ => by simp [hγ])
        (fun hβ => absurd h_pos hβ)]
      simp
    ·
      classical
      refine ⟨fun γ => if γ = -β then N else 0, ?_⟩
      rw [Finset.sum_eq_single (-β)
        (fun γ _ hγ => by simp [hγ])
        (fun hβ => absurd h_neg hβ)]
      simp

end
