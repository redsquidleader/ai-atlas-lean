/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Atlas.NumberTheoryI.code.KroneckerWeber
import Atlas.NumberTheoryI.code.AdicCompletionAlgebra

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField.Adeles

inductive Place (K : Type*) [Field K] [NumberField K] where
  | finite : HeightOneSpectrum (𝓞 K) → Place K
  | infinite : InfinitePlace K → Place K

instance instDecidableEqPlace (K : Type*) [Field K] [NumberField K] :
    DecidableEq (Place K) :=
  Classical.decEq _

variable {K : Type*} [Field K] [NumberField K]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem adicCompletion_finite_residueField
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (KroneckerWeber.completion_residueFieldEquiv (𝓞 K) K v).symm.toEquiv

noncomputable instance adicCompletion_compactSpace_integer
    (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (Valued.integer (v.adicCompletion K)) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  exact ⟨(Valued.isClosed_integer _).completeSpace_coe,
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
    adicCompletion_finite_residueField K v⟩

noncomputable instance adicCompletion_properSpace
    (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  letI := Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact Valued.integer.properSpace_iff_compactSpace_integer.mpr
    (adicCompletion_compactSpace_integer v)

lemma isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
  change IsCompact (Valued.integer (v.adicCompletion K) : Set (v.adicCompletion K))
  have := (adicCompletion_compactSpace_integer v).isCompact_univ
  rwa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_val] at this

abbrev adeleRing := AdeleRing (𝓞 K) K

def placeNorm (v : Place K) (x : K) : ℝ :=
  match v with
  | .finite vi => NumberField.HeightOneSpectrum.adicAbv K vi x
  | .infinite w => w x

lemma placeNorm_mul (v : Place K) (x y : K) :
    placeNorm v (x * y) = placeNorm v x * placeNorm v y := by
  match v with
  | .finite vi => exact map_mul (NumberField.HeightOneSpectrum.adicAbv K vi) x y
  | .infinite w => exact w.1.map_mul x y

lemma placeNorm_nonneg (v : Place K) (x : K) : 0 ≤ placeNorm v x := by
  match v with
  | .finite vi => exact (NumberField.HeightOneSpectrum.adicAbv K vi).nonneg x
  | .infinite w => exact w.1.nonneg x

def placeNormAdele (v : Place K) (a : adeleRing (K := K)) : ℝ :=
  match v with
  | .finite vi => ‖a.2 vi‖
  | .infinite w => ‖a.1 w‖

lemma placeNorm_eq_placeNormAdele_algebraMap (v : Place K) (x : K) :
    placeNorm v x = placeNormAdele v (algebraMap K (adeleRing (K := K)) x) := by
  match v with
  | .infinite w =>
    show w x = ‖(algebraMap K (InfiniteAdeleRing K) x) w‖
    rw [show (algebraMap K (InfiniteAdeleRing K) x) w = algebraMap K w.Completion x from rfl]
    rw [show algebraMap K w.Completion x =
      (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe]
    simp
  | .finite vi =>
    show NumberField.HeightOneSpectrum.adicAbv K vi x =
      ‖(algebraMap K (adeleRing (K := K)) x).2 vi‖
    rw [show (algebraMap K (adeleRing (K := K)) x).2 vi =
      algebraMap K (vi.adicCompletion K) x from rfl]
    rw [show algebraMap K (vi.adicCompletion K) x = FinitePlace.embedding vi x from rfl]
    rw [FinitePlace.norm_embedding]

def adelicAbsVal (a : adeleRing (K := K)) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) *
  (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖)

section RestrictedProductDirectLimit

open Filter Set Topology

theorem restrictedProduct_topology_eq_iSup {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    (𝓕 : Filter ι) :
    RestrictedProduct.topologicalSpace X U 𝓕 =
      ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
        TopologicalSpace.coinduced (RestrictedProduct.inclusion X U hS)
          (RestrictedProduct.topologicalSpace X U (𝓟 S)) :=
  RestrictedProduct.topologicalSpace_eq_iSup 𝓕

open scoped RestrictedProduct in
theorem restrictedProduct_inclusion_isEmbedding {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    {𝓕 : Filter ι} {S : Set ι} (hS : 𝓕 ≤ 𝓟 S) :
    Topology.IsEmbedding (RestrictedProduct.inclusion X U hS) :=
  RestrictedProduct.isEmbedding_inclusion_principal hS

open scoped RestrictedProduct in
theorem restrictedProduct_inclusion_isOpenEmbedding {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    (hU_open : ∀ i, IsOpen (U i))
    {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    Topology.IsOpenEmbedding (RestrictedProduct.inclusion X U hS) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal hU_open hS

open scoped RestrictedProduct in
theorem restrictedProduct_continuous_iff {ι : Type*}
    (X : ι → Type*) (U : (i : ι) → Set (X i)) [∀ i, TopologicalSpace (X i)]
    {𝓕 : Filter ι}
    {Y : Type*} [TopologicalSpace Y]
    {f : (Πʳ i, [X i, U i]_[𝓕]) → Y} :
    Continuous f ↔
      ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
        Continuous (f ∘ RestrictedProduct.inclusion X U hS) :=
  RestrictedProduct.continuous_dom

theorem finiteAdeleRing_topology_eq_iSup :
    RestrictedProduct.topologicalSpace
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K))
      cofinite =
    ⨆ (S : Set (HeightOneSpectrum (𝓞 K))) (hS : cofinite ≤ 𝓟 S),
      TopologicalSpace.coinduced
        (RestrictedProduct.inclusion
          (fun v => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) hS)
        (RestrictedProduct.topologicalSpace
          (fun v => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) (𝓟 S)) :=
  RestrictedProduct.topologicalSpace_eq_iSup cofinite

theorem finiteAdeleRing_inclusion_isOpenEmbedding
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : cofinite ≤ 𝓟 S) :
    Topology.IsOpenEmbedding
      (RestrictedProduct.inclusion
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => ↑(v.adicCompletionIntegers K)) hS) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1) hS

end RestrictedProductDirectLimit

instance adeleRing_isTopologicalRing : IsTopologicalRing (adeleRing (K := K)) :=
  inferInstance

instance infiniteAdeleRing_t2Space : T2Space (InfiniteAdeleRing K) := Pi.t2Space

instance finiteAdeleRing_t2Space : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite))

instance adeleRing_t2Space : T2Space (adeleRing (K := K)) :=
  Prod.t2Space

instance finiteAdeleRing_locallyCompactSpace :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by


  letI wlcs : WeaklyLocallyCompactSpace (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite) :=
    RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
      (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1)
      (Filter.Eventually.of_forall (fun v => isCompact_adicCompletionIntegers v))

  letI : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := wlcs

  infer_instance

instance adeleRing_locallyCompactSpace : LocallyCompactSpace (adeleRing (K := K)) :=
  Prod.locallyCompactSpace _ _

theorem diag_injective : Function.Injective (algebraMap K (adeleRing (K := K))) :=
  AdeleRing.algebraMap_injective (𝓞 K) K

abbrev principalSubgroup : AddSubgroup (adeleRing (K := K)) :=
  AdeleRing.principalSubgroup (𝓞 K) K

lemma eq_zero_of_integral_and_inf_lt_one (k : 𝓞 K)
    (hinf : ∀ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) < 1) :
    k = 0 := by
  suffices h : (algebraMap (𝓞 K) K) k = 0 from Subtype.coe_injective h
  by_contra hk
  have h_prod_lt : ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) ^ w.mult < 1 := by
    classical
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    rw [(Finset.mul_prod_erase Finset.univ
        (fun w : InfinitePlace K => w (algebraMap (𝓞 K) K k) ^ w.mult)
        (Finset.mem_univ w₀)).symm]
    calc _ ≤ (w₀ (algebraMap (𝓞 K) K k) ^ w₀.mult) * 1 := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.prod_le_one
            · intro w _; exact pow_nonneg (w.1.nonneg _) _
            · intro w _; exact pow_le_one₀ (w.1.nonneg _) (le_of_lt (hinf w))
          · exact le_of_lt (pow_pos (w₀.1.pos hk) _)
        _ = w₀ (algebraMap (𝓞 K) K k) ^ w₀.mult := mul_one _
        _ < 1 := pow_lt_one₀ (w₀.1.nonneg _) (hinf w₀) w₀.mult_pos.ne'
  have h_prod := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K k)
  have h_norm_loc : (Algebra.norm ℚ) ((algebraMap (𝓞 K) K) k) =
    algebraMap ℤ ℚ ((Algebra.norm ℤ) k) :=
    Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ) k
  rw [h_norm_loc] at h_prod; rw [h_prod] at h_prod_lt
  have h_norm_zero : (Algebra.norm ℤ) k = 0 := by
    by_contra hn
    have h1 : |(((Algebra.norm ℤ) k : ℤ) : ℝ)| < 1 := by
      have : ((Algebra.norm ℤ k : ℤ) : ℝ) =
        ((algebraMap ℤ ℚ ((Algebra.norm ℤ) k) : ℚ) : ℝ) := rfl
      rw [this]; exact_mod_cast h_prod_lt
    have h2 := abs_lt.mp h1
    have h3 : (-1 : ℤ) < (Algebra.norm ℤ) k := by exact_mod_cast h2.1
    have h4 : ((Algebra.norm ℤ) k : ℤ) < 1 := by exact_mod_cast h2.2
    omega
  rw [Algebra.norm_eq_zero_iff] at h_norm_zero
  exact hk (by simp [h_norm_zero])

lemma mem_ringOfIntegers_of_finiteAdele_integral (x : K)
    (h : algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈
      Set.range (RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite)) :
    x ∈ (algebraMap (𝓞 K) K).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one K x
  intro v
  obtain ⟨a, ha⟩ := h
  suffices Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1 by
    rwa [show Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x from by
      rw [v.valuedAdicCompletion_def K]
      show Valued.extensionValuation ((x : v.adicCompletion K)) = _
      rw [Valued.extensionValuation_apply_coe]; rfl] at this
  change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) x).val v) ≤ 1
  rw [show (algebraMap K (FiniteAdeleRing (𝓞 K) K) x).val v =
    (RestrictedProduct.structureMap _ _ _ a).val v from
    congr_arg (fun y => y.val v) ha.symm]
  exact (a v).prop

theorem principalAdeles_discrete :
    DiscreteTopology (principalSubgroup (K := K)) := by
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  let U_inf := {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1}
  let U_fin := Set.range (RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite)
  refine ⟨U_inf ×ˢ U_fin, ?_, ?_⟩
  ·
    apply IsOpen.prod
    ·
      change IsOpen {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1}
      have : {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1} =
          ⋂ w, {f : InfiniteAdeleRing K | ‖f w‖ < 1} := by
        ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this]
      exact isOpen_iInter_of_finite (fun w =>
        isOpen_lt (continuous_norm.comp (continuous_apply w)) continuous_const)
    ·
      exact (RestrictedProduct.isOpenEmbedding_structureMap
        (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1)).isOpen_range
  ·
    ext ⟨a, ha⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, AddSubgroup.mk_eq_zero]
    constructor
    ·
      intro ⟨h_inf, h_fin⟩
      obtain ⟨x, hx⟩ := ha

      have hx_int : x ∈ (algebraMap (𝓞 K) K).range := by
        apply mem_ringOfIntegers_of_finiteAdele_integral
        rw [show algebraMap K (FiniteAdeleRing (𝓞 K) K) x = a.2 from by rw [← hx]; rfl]
        exact h_fin
      obtain ⟨k, hk⟩ := hx_int

      have hinf : ∀ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) < 1 := by
        intro w
        have hw := h_inf w
        rw [hk]
        have ha1 : a.1 = algebraMap K (InfiniteAdeleRing K) x := by rw [← hx]; rfl
        rw [ha1] at hw
        rw [show (algebraMap K (InfiniteAdeleRing K) x w : w.Completion) =
          algebraMap K w.Completion x from rfl] at hw
        rwa [show ‖algebraMap K w.Completion x‖ = w x from by
          rw [show algebraMap K w.Completion x =
            (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
          rw [InfinitePlace.Completion.norm_coe]; simp] at hw

      have hk0 := eq_zero_of_integral_and_inf_lt_one k hinf
      rw [← hx, ← hk, hk0, map_zero, map_zero]
    ·
      intro h0; subst h0
      exact ⟨fun w => by show ‖(0 : w.Completion)‖ < 1; rw [norm_zero]; exact one_pos,
             ⟨0, by ext v; rfl⟩⟩

instance infinitePlace_properSpace (v : InfinitePlace K) :
    ProperSpace v.Completion := by
  open InfinitePlace.Completion in
  constructor
  intro x r
  rcases v.isReal_or_isComplex with hv | hv
  · have e := isometryEquivRealOfIsReal hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩
  · have e := isometryEquivComplexOfIsComplex hv
    rw [show Metric.closedBall x r = e.symm '' (Metric.closedBall (e x) r) from ?_]
    · exact (isCompact_closedBall (e x) r).image e.symm.continuous
    · ext y; simp only [Set.mem_image, Metric.mem_closedBall]
      exact ⟨fun h => ⟨e y, by rwa [e.dist_eq], by simp⟩,
             fun ⟨z, hz, hzy⟩ => by rw [← hzy, ← e.dist_eq]; simpa using hz⟩

lemma isCompact_finiteAdeleRing_integralSet :
    IsCompact {a : FiniteAdeleRing (𝓞 K) K |
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} := by
  have heq : {a : FiniteAdeleRing (𝓞 K) K |
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} =
      Set.range (RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => ↑(v.adicCompletionIntegers K))
        Filter.cofinite) := by
    rw [RestrictedProduct.range_structureMap]
    ext a; simp only [Set.mem_setOf_eq]
    exact ⟨fun h v => h v, fun h v => h v⟩
  rw [heq]
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ↑(v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v; change CompactSpace (Valued.integer (v.adicCompletion K)); infer_instance
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

lemma adeles_integral_set_compact :
    IsCompact
      ((Set.pi Set.univ (fun (v : InfinitePlace K) =>
        Metric.closedBall (0 : v.Completion) 1)) ×ˢ
       {a : FiniteAdeleRing (𝓞 K) K |
         ∀ v : HeightOneSpectrum (𝓞 K),
           a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}) := by
  apply IsCompact.prod
  · exact isCompact_univ_pi (fun v => isCompact_closedBall 0 1)
  · exact isCompact_finiteAdeleRing_integralSet


lemma valued_algebraMap_eq_valuation_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = (v.valuation K) x := by
  rw [show algebraMap K (v.adicCompletion K) x =
    ↑((WithVal.equiv (v.valuation K)).symm x) from rfl]
  exact v.valuedAdicCompletion_eq_valuation' x

lemma algebraMap_div_mem_adicCompletionIntegers_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (r d : 𝓞 K)
    (h : v.intValuation r ≤ v.intValuation d) :
    algebraMap K (v.adicCompletion K) ((r : K) / (d : K)) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  show Valued.v (algebraMap K (v.adicCompletion K) ((r : K) / (d : K))) ≤ 1
  rw [valued_algebraMap_eq_valuation_crt, map_div₀,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact div_le_one_of_le₀ h (WithZero.zero_le _)

lemma intValuation_le_exp_of_mem_pow_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (n : ℕ)
    (hr : r ∈ v.asIdeal ^ n) : v.intValuation r ≤ WithZero.exp (-↑n) := by
  rw [v.intValuation_le_pow_iff_dvd]
  rwa [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]

lemma intValuation_le_of_mem_pow_ge_crt {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (r d : 𝓞 K) (hd : d ≠ 0)
    (n : ℕ) (hn : ((-WithZero.log (v.intValuation d)).toNat) ≤ n)
    (hr : r ∈ v.asIdeal ^ n) :
    v.intValuation r ≤ v.intValuation d := by
  have hne := HeightOneSpectrum.intValuation_ne_zero v d hd
  have hle : WithZero.log (v.intValuation d) ≤ 0 := by
    have h1 := v.intValuation_le_one d
    rw [← WithZero.exp_log hne] at h1
    rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  calc v.intValuation r
      ≤ WithZero.exp (-↑n) := intValuation_le_exp_of_mem_pow_crt v r n hr
    _ ≤ WithZero.exp (-↑((-WithZero.log (v.intValuation d)).toNat)) := by
        rw [WithZero.exp_le_exp]; omega
    _ = v.intValuation d := by
        conv_rhs => rw [← WithZero.exp_log hne]
        congr 1; rw [Int.toNat_of_nonneg (neg_nonneg.mpr hle), neg_neg]

set_option maxHeartbeats 800000 in
lemma exists_integral_approx_at_place {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    ∃ c : K, (x - algebraMap K (v.adicCompletion K) c) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  set U := (fun y => x - y) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hU_open : IsOpen U :=
    (continuous_const.sub continuous_id).isOpen_preimage _ (Valued.isOpen_valuationSubring _)
  have hU_ne : U.Nonempty :=
    ⟨x, show x - x ∈ (v.adicCompletionIntegers K : Set _) by
      rw [sub_self]; exact (v.adicCompletionIntegers K).zero_mem⟩
  obtain ⟨c, hc⟩ := (v.denseRange_algebraMap K).exists_mem_open hU_open hU_ne
  exact ⟨c, hc⟩

set_option maxHeartbeats 3200000 in
theorem crt_finite_places_covering (K : Type*) [Field K] [NumberField K]
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ c : K, ∀ v : HeightOneSpectrum (𝓞 K),
      (a v - algebraMap K (v.adicCompletion K) c) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  classical

  have ha := a.property
  rw [Filter.eventually_cofinite] at ha
  let S := ha.toFinset

  have hdense : ∀ v : HeightOneSpectrum (𝓞 K), ∃ c : K,
      (a v - algebraMap K (v.adicCompletion K) c) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => exists_integral_approx_at_place v (a v)
  choose c_all hc_all using hdense

  obtain ⟨⟨d, hd_mem⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (S.image c_all)
  have hd_ne : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero hd_mem
  have hd_K_ne : ((d : 𝓞 K) : K) ≠ 0 := by exact_mod_cast hd_ne

  have hn_exists : ∀ v ∈ S, ∃ n : 𝓞 K,
      algebraMap (𝓞 K) K n = (d : 𝓞 K) • c_all v :=
    fun v hv => hd _ (Finset.mem_image_of_mem _ hv)

  let e : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => (-WithZero.log (v.intValuation d)).toNat

  have hT_finite : Set.Finite {v : HeightOneSpectrum (𝓞 K) | d ∈ v.asIdeal} := by
    have hI : Ideal.span ({d} : Set (𝓞 K)) ≠ 0 := by simp [hd_ne]
    exact (Ideal.finite_factors hI).subset
      (fun v hv => Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv)))
  let T := hT_finite.toFinset \ S
  let ST := S ∪ T


  let hn_exists' : ∀ v ∈ S, 𝓞 K := fun v hv => (hn_exists v hv).choose
  have hn_spec : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S),
      algebraMap (𝓞 K) K (hn_exists' v hv) = (d : 𝓞 K) • c_all v :=
    fun v hv => (hn_exists v hv).choose_spec
  let target : {v // v ∈ ST} → 𝓞 K := fun ⟨v, hv⟩ =>
    if h : v ∈ S then hn_exists' v h else 0
  have hprime : ∀ i ∈ ST, Prime ((id i : HeightOneSpectrum (𝓞 K)).asIdeal) :=
    fun i _ => i.prime
  have hcoprime : ∀ i ∈ ST, ∀ j ∈ ST, i ≠ j →
      (id i : HeightOneSpectrum (𝓞 K)).asIdeal ≠ (id j).asIdeal :=
    fun _ _ _ _ h heq => h (HeightOneSpectrum.ext heq)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) e hprime hcoprime target

  refine ⟨(y : K) / (d : K), fun v => ?_⟩
  by_cases hv_in_S : v ∈ S
  ·
    have hv_ST : v ∈ ST := Finset.mem_union_left T hv_in_S
    have hy_v := hy v hv_ST


    have htarget : target ⟨v, hv_ST⟩ = hn_exists' v hv_in_S := dif_pos hv_in_S
    rw [htarget] at hy_v

    have hmem_neg : hn_exists' v hv_in_S - y ∈ v.asIdeal ^ e v := by
      rw [show hn_exists' v hv_in_S - y = -(y - hn_exists' v hv_in_S) from by ring]
      exact neg_mem hy_v

    have hval_le : v.intValuation (hn_exists' v hv_in_S - y) ≤ v.intValuation d :=
      intValuation_le_of_mem_pow_ge_crt v (hn_exists' v hv_in_S - y) d hd_ne (e v) le_rfl hmem_neg

    have hdiv_mem : algebraMap K (v.adicCompletion K)
        ((hn_exists' v hv_in_S - y : 𝓞 K) / (d : K)) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      algebraMap_div_mem_adicCompletionIntegers_crt v _ d hval_le


    have hc_v_eq : c_all v = (hn_exists' v hv_in_S : K) / (d : K) := by
      have := hn_spec v hv_in_S
      rw [Algebra.smul_def] at this
      rw [eq_div_iff hd_K_ne, mul_comm]
      exact this.symm
    rw [show (y : K) / (d : K) = c_all v + ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K) from by
      rw [hc_v_eq]; field_simp; ring]
    rw [show a v - algebraMap K (v.adicCompletion K)
        (c_all v + ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K)) =
      (a v - algebraMap K (v.adicCompletion K) (c_all v)) -
        algebraMap K (v.adicCompletion K) (((y : K) - (hn_exists' v hv_in_S : K)) / (d : K)) from by
      simp only [map_add]; ring]
    apply sub_mem (hc_all v)


    rw [show ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K) =
      -((hn_exists' v hv_in_S : K) - (y : K)) / (d : K) from by ring]
    rw [neg_div]
    rw [map_neg]
    exact neg_mem hdiv_mem
  ·


    have hav : a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      by_contra h
      exact hv_in_S (ha.mem_toFinset.mpr h)

    suffices h_yd : algebraMap K (v.adicCompletion K) ((y : K) / (d : K)) ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) from by
      have := sub_mem hav h_yd
      convert this using 1
    by_cases hv_d : d ∈ v.asIdeal
    ·
      have hv_T : v ∈ T := by
        simp only [T, Finset.mem_sdiff]
        exact ⟨hT_finite.mem_toFinset.mpr hv_d, hv_in_S⟩
      have hv_ST : v ∈ ST := Finset.mem_union_right S hv_T
      have hy_v := hy v hv_ST
      have htarget : target ⟨v, hv_ST⟩ = 0 := dif_neg hv_in_S
      rw [htarget] at hy_v
      simp only [sub_zero] at hy_v

      exact algebraMap_div_mem_adicCompletionIntegers_crt v y d
        (intValuation_le_of_mem_pow_ge_crt v y d hd_ne (e v) le_rfl hy_v)
    ·
      have hval_d : v.intValuation d = 1 :=
        HeightOneSpectrum.intValuation_eq_one_iff.mpr hv_d
      exact algebraMap_div_mem_adicCompletionIntegers_crt v y d
        (by rw [hval_d]; exact v.intValuation_le_one y)

open scoped Classical in
noncomputable def coveringBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  max 1 (∑ i, ‖mixedEmbedding.latticeBasis K i‖)

lemma one_le_coveringBound (K : Type*) [Field K] [NumberField K] :
    1 ≤ coveringBound K :=
  le_max_left 1 _

lemma coveringBound_pos (K : Type*) [Field K] [NumberField K] :
    0 < coveringBound K :=
  lt_of_lt_of_le one_pos (one_le_coveringBound K)

lemma coveringBound_ne_zero (K : Type*) [Field K] [NumberField K] :
    coveringBound K ≠ 0 :=
  ne_of_gt (coveringBound_pos K)

lemma coveringBound_nonneg (K : Type*) [Field K] [NumberField K] :
    0 ≤ coveringBound K :=
  le_of_lt (coveringBound_pos K)

open scoped Classical in
open NumberField.InfiniteAdeleRing NumberField.InfinitePlace.Completion
  NumberField.mixedEmbedding NumberField.InfinitePlace in
lemma lattice_covering_infinite_places (K : Type*) [Field K] [NumberField K]
    (f : InfiniteAdeleRing K) (c₁ : K) :
    ∃ r : 𝓞 K, ∀ w : InfinitePlace K,
      ‖f w - algebraMap K w.Completion (c₁ + algebraMap (𝓞 K) K r)‖ ≤
        coveringBound K := by

  set g := ringEquiv_mixedSpace K (f - algebraMap K _ c₁) with hg_def

  set fl := ZSpan.floor (latticeBasis K) g

  have fl_mem : (fl : mixedSpace K) ∈
      Submodule.span ℤ (Set.range (latticeBasis K)) := fl.property
  rw [mem_span_latticeBasis] at fl_mem
  change (fl : mixedSpace K) ∈
    ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap.range at fl_mem
  obtain ⟨r, hr⟩ := fl_mem
  have hr' : mixedEmbedding K (algebraMap (𝓞 K) K r) = (fl : mixedSpace K) := by
    exact_mod_cast hr
  refine ⟨r, fun w => ?_⟩

  set fract_g := ZSpan.fract (latticeBasis K) g with hfract_def
  set diff := f - algebraMap K _ (c₁ + algebraMap (𝓞 K) K r) with hdiff_def

  have halg : ringEquiv_mixedSpace K diff = fract_g := by
    rw [hfract_def, ZSpan.fract_apply, hdiff_def]
    have key : ringEquiv_mixedSpace K (f - algebraMap K _ (c₁ + algebraMap (𝓞 K) K r)) =
        g - mixedEmbedding K (algebraMap (𝓞 K) K r) := by
      simp only [hg_def, map_sub, map_add, mixedEmbedding_eq_algebraMap_comp]
      ring
    rw [key, hr']

  have hfract_bound : ‖fract_g‖ ≤ coveringBound K :=
    le_trans (ZSpan.norm_fract_le (latticeBasis K) g) (le_max_right _ _)

  suffices h : ‖diff w‖ ≤ ‖fract_g‖ by
    simp only [hdiff_def] at h
    exact le_trans h hfract_bound

  by_cases hw : w.IsReal
  ·
    have heq : extensionEmbeddingOfIsReal hw (diff w) = fract_g.1 ⟨w, hw⟩ := by
      have := congr_arg Prod.fst halg
      simp [ringEquiv_mixedSpace_apply] at this
      exact congr_fun this ⟨w, hw⟩
    rw [← (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), heq]
    exact le_trans (norm_le_pi_norm fract_g.1 ⟨w, hw⟩) (le_max_left _ _)
  ·
    have hwc := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw
    have heq : extensionEmbedding w (diff w) = fract_g.2 ⟨w, hwc⟩ := by
      have := congr_arg Prod.snd halg
      simp [ringEquiv_mixedSpace_apply] at this
      exact congr_fun this ⟨w, hwc⟩
    rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), heq]
    exact le_trans (norm_le_pi_norm fract_g.2 ⟨w, hwc⟩) (le_max_right _ _)

lemma crt_covering (a : adeleRing (K := K)) :
    ∃ c : K,
      (∀ w : InfinitePlace K, ‖a.1 w - algebraMap K w.Completion c‖ ≤
        coveringBound K) ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        (a.2 v - algebraMap K (v.adicCompletion K) c) ∈
          (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by

  obtain ⟨c₁, hfin₁⟩ := crt_finite_places_covering K a.2

  obtain ⟨r, hinf⟩ := lattice_covering_infinite_places K a.1 c₁

  refine ⟨c₁ + algebraMap (𝓞 K) K r, hinf, fun v => ?_⟩


  rw [map_add]
  have h1 : a.2 v - algebraMap K (v.adicCompletion K) c₁ ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := hfin₁ v
  have h2 : algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    change (algebraMap (𝓞 K) (v.adicCompletion K) r : v.adicCompletion K) ∈ _
    exact v.coe_mem_adicCompletionIntegers r
  have : a.2 v - (algebraMap K (v.adicCompletion K) c₁ +
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r)) =
      (a.2 v - algebraMap K (v.adicCompletion K) c₁) -
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) := by ring
  rw [this]
  exact sub_mem h1 h2

theorem adeles_compact_fundamental_domain :
    ∃ W : Set (adeleRing (K := K)), IsCompact W ∧
      ∀ a : adeleRing (K := K), ∃ c : K, a - algebraMap K _ c ∈ W := by

  refine ⟨(Set.pi Set.univ (fun (v : InfinitePlace K) =>
      Metric.closedBall (0 : v.Completion) (coveringBound K))) ×ˢ
     {a : FiniteAdeleRing (𝓞 K) K |
       ∀ v : HeightOneSpectrum (𝓞 K),
         a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}, ?_, ?_⟩
  ·
    apply IsCompact.prod
    · exact isCompact_univ_pi (fun v => isCompact_closedBall 0 (coveringBound K))
    · exact isCompact_finiteAdeleRing_integralSet

  ·
    intro a
    obtain ⟨c, hinf, hfin⟩ := crt_covering a
    exact ⟨c, ⟨fun w _ => by
      simp only [Metric.mem_closedBall, dist_zero_right]; exact hinf w, fun v => hfin v⟩⟩

theorem principalAdeles_cocompact :
    CompactSpace ((adeleRing (K := K)) ⧸ (principalSubgroup (K := K))) := by
  obtain ⟨W, hW_compact, hW_surj⟩ := adeles_compact_fundamental_domain (K := K)
  rw [← isCompact_univ_iff]
  have himg : Set.univ = (QuotientAddGroup.mk (s := principalSubgroup (K := K))) '' W := by
    ext q
    simp only [Set.mem_univ, true_iff, Set.mem_image]
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨c, hc⟩ := hW_surj a
    refine ⟨a - algebraMap K _ c, hc, ?_⟩
    simp only [QuotientAddGroup.mk_sub]
    rw [sub_eq_self]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨c, rfl⟩
  rw [himg]
  exact hW_compact.image continuous_quotient_mk'

def PiTensorCompletion (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L] :=
  (v : InfinitePlace K) → (L ⊗[K] v.Completion)

instance piTensorCompletion_commRing (K L : Type*)
    [Field K] [NumberField K] [Field L] [Algebra K L] :
    CommRing (PiTensorCompletion K L) := Pi.commRing

attribute [local instance] WithAbs.algebraLeft

set_option backward.isDefEq.respectTransparency false in
noncomputable def tensorCompletionToFiberProd
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    L ⊗[K] v.Completion →+*
      ((w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) := by
  apply Pi.ringHom
  intro ⟨w, hw⟩
  letI : Algebra K w.Completion := Algebra.restrictScalars K L w.Completion
  haveI : IsScalarTower K L w.Completion := by
    constructor; intro x y z; change (x • y) • z = x • (y • z); simp [smul_assoc]
  haveI : w.1.LiesOver v.1 := ⟨by
    have h1 : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← h1]; rfl⟩
  haveI itv : IsTopologicalRing (WithAbs v.1) := inferInstance
  haveI itw : IsTopologicalRing (WithAbs w.1) := inferInstance
  haveI uv : IsUniformAddGroup (WithAbs v.1) := inferInstance
  haveI uw : IsUniformAddGroup (WithAbs w.1) := inferInstance
  have hiso := InfinitePlace.LiesOver.isometry_algebraMap w (v := v)
  let isoHom : v.Completion →+* w.Completion :=
    @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
      (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
  let vToW : v.Completion →ₐ[K] w.Completion := {
    toRingHom := isoHom
    commutes' := by
      intro r
      change @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
        (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
        (↑(algebraMap K (WithAbs v.1) r)) = algebraMap K w.Completion r
      rw [@Isometry.mapRingHom_coe _ _ _ _ itv uv _ _ uw itw _ hiso]
      congr 1
  }
  let lToW : L →ₐ[K] w.Completion := {
    toRingHom := algebraMap L w.Completion
    commutes' := fun _ => rfl
  }
  exact (Algebra.TensorProduct.productMap lToW vToW).toRingHom


theorem tensorCompletionToFiberProd_bijective
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (v : InfinitePlace K) :
    Function.Bijective (tensorCompletionToFiberProd K L v) := by sorry

set_option backward.isDefEq.respectTransparency false in
theorem infinitePlace_baseChange_decomposition (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : InfinitePlace K) :
    ∃ (e : (L ⊗[K] v.Completion) ≃+*
      ((w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion)),
      ∀ (l : L), e (l ⊗ₜ[K] (1 : v.Completion)) =
        fun (w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) =>
          algebraMap L w.val.Completion l := by
  let e := RingEquiv.ofBijective (tensorCompletionToFiberProd K L v)
    (tensorCompletionToFiberProd_bijective K L v)
  exact ⟨e, fun l => by
    ext ⟨w, hw⟩
    show tensorCompletionToFiberProd K L v (l ⊗ₜ[K] 1) ⟨w, hw⟩ = algebraMap L w.Completion l
    simp only [tensorCompletionToFiberProd, Pi.ringHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  ⟩

def sigmaPiRegroup (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ((v : InfinitePlace K) →
      (w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) ≃+*
    InfiniteAdeleRing L :=
  RingEquiv.mk
    { toFun := fun g w => g (w.comap (algebraMap K L)) ⟨w, rfl⟩
      invFun := fun h _v ⟨w, _⟩ => h w
      left_inv := fun g => by ext v ⟨w, hw⟩; subst hw; rfl
      right_inv := fun _ => rfl }
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem completion_tensor_pi_equiv (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    ∃ (e : PiTensorCompletion K L ≃+* InfiniteAdeleRing L),
      ∀ (l : L), e (fun v => l ⊗ₜ[K] (1 : v.Completion)) =
        algebraMap L (InfiniteAdeleRing L) l := by
  classical

  choose e_v he_v using fun v => infinitePlace_baseChange_decomposition K L v

  let step1 : PiTensorCompletion K L ≃+*
      ((v : InfinitePlace K) →
        (w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) :=
    RingEquiv.piCongrRight e_v

  let step2 := sigmaPiRegroup K L
  refine ⟨step1.trans step2, fun l => ?_⟩
  funext w
  show step2 (step1 (fun v => l ⊗ₜ[K] (1 : v.Completion))) w =
    algebraMap L (InfiniteAdeleRing L) l w
  exact congr_fun (he_v (w.comap (algebraMap K L)) l) ⟨w, rfl⟩

open scoped Classical in
theorem infiniteAdeleRing_base_change_iso (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Nonempty ((InfiniteAdeleRing K ⊗[K] L) ≃+* InfiniteAdeleRing L) := by
  classical

  let comm_iso := (Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L).toRingEquiv

  let pi_iso := (Algebra.TensorProduct.piRight K K L
    (fun v : InfinitePlace K => v.Completion)).toRingEquiv

  obtain ⟨fiber_iso, _⟩ := completion_tensor_pi_equiv K L

  exact ⟨comm_iso.trans (pi_iso.trans fiber_iso)⟩


instance finAdeleRing_algebra_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L)).toAlgebra

instance finAdeleRing_scalarTower_base_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K K (FiniteAdeleRing (𝓞 L) L) :=
  ⟨fun r s x => by simp [Algebra.smul_def, mul_assoc]⟩

instance finAdeleRing_scalarTower_base_ext (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) := by
  constructor; intro r l x; simp only [Algebra.smul_def]; rw [map_mul, mul_assoc]; rfl

noncomputable def primeBelow (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
  isPrime := Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))
  ne_bot := by intro h; exact w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)

noncomputable def localBaseChangeMap (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    WithVal (HeightOneSpectrum.valuation K (primeBelow K L w)) →+*
      w.adicCompletion L :=
  (UniformSpace.Completion.coeRingHom (α := WithVal (HeightOneSpectrum.valuation L w))).comp
    ((WithVal.equiv (HeightOneSpectrum.valuation L w)).symm.toRingHom.comp
      ((algebraMap K L).comp
        (WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))).toRingHom))

lemma localBaseChangeMap_continuous (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (localBaseChangeMap K L w) := by
  set v := primeBelow K L w
  set g : WithVal (HeightOneSpectrum.valuation K v) →+*
      WithVal (HeightOneSpectrum.valuation L w) :=
    (WithVal.equiv (HeightOneSpectrum.valuation L w)).symm.toRingHom.comp
      ((algebraMap K L).comp
        (WithVal.equiv (HeightOneSpectrum.valuation K v)).toRingHom) with hg_def

  show Continuous (UniformSpace.Completion.coeRingHom.comp g)
  apply Continuous.comp (UniformSpace.Completion.continuous_coe _)


  exact algebraMap_withVal_continuous_general K v w (le_refl _)

noncomputable def baseChangeAtPrime (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    (primeBelow K L w).adicCompletion K →+* w.adicCompletion L :=
  UniformSpace.Completion.extensionHom
    (localBaseChangeMap K L w) (localBaseChangeMap_continuous K L w)

lemma baseChangeAtPrime_mem_integers (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L))
    (x : (primeBelow K L w).adicCompletion K)
    (hx : x ∈ (primeBelow K L w).adicCompletionIntegers K) :
    (baseChangeAtPrime K L w) x ∈ w.adicCompletionIntegers L := by

  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx


  have hclosed : IsClosed {y : (primeBelow K L w).adicCompletion K |
      Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
    have h1 : {y : (primeBelow K L w).adicCompletion K |
        Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
        {y | ¬(Valued.v y ≤ 1)} ∪ {y | Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
    rw [h1]
    apply IsClosed.union
    ·
      have : {y : (primeBelow K L w).adicCompletion K | ¬(Valued.v y ≤ 1)} =
          ((Valued.v.valuationSubring :
            ValuationSubring ((primeBelow K L w).adicCompletion K)) :
            Set ((primeBelow K L w).adicCompletion K))ᶜ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClopen_valuationSubring
        ((primeBelow K L w).adicCompletion K)).2.isClosed_compl
    ·
      have hf_cont : Continuous (baseChangeAtPrime K L w) :=
        UniformSpace.Completion.continuous_extension
      have : {y : (primeBelow K L w).adicCompletion K |
          Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
          (baseChangeAtPrime K L w :
            (primeBelow K L w).adicCompletion K → w.adicCompletion L) ⁻¹'
            ((Valued.v.valuationSubring : ValuationSubring (w.adicCompletion L)) :
              Set (w.adicCompletion L)) := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClosed_valuationSubring (w.adicCompletion L)).preimage hf_cont

  have hdense : ∀ (k : WithVal (HeightOneSpectrum.valuation K (primeBelow K L w))),
      Valued.v (↑k : (primeBelow K L w).adicCompletion K) ≤ 1 →
        Valued.v ((baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K)) ≤ 1 := by
    intro k hk
    rw [Valued.valuedCompletion_apply] at hk

    have hf_coe : (baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K) =
        localBaseChangeMap K L w k :=
      UniformSpace.Completion.extensionHom_coe _ (localBaseChangeMap_continuous K L w) k
    rw [hf_coe]


    have hval : Valued.v ((localBaseChangeMap K L w) k) =
        HeightOneSpectrum.valuation L w (algebraMap K L
          ((WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))) k)) := by
      simp only [localBaseChangeMap, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      erw [Valued.valuedCompletion_apply]
      rw [← WithVal.val_apply_equiv (HeightOneSpectrum.valuation L w)]
      simp only [RingEquiv.apply_symm_apply]
    rw [hval]


    haveI : w.asIdeal.LiesOver (primeBelow K L w).asIdeal := ⟨rfl⟩
    rw [valuation_extends_with_ramificationIdx K L (primeBelow K L w) w]
    rw [WithVal.val_apply_equiv]
    exact pow_le_one₀ (WithZero.zero_le _) hk


  exact UniformSpace.Completion.induction_on x hclosed (fun k => hdense k) hx

lemma baseChange_restricted_condition (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∀ᶠ (w : HeightOneSpectrum (𝓞 L)) in Filter.cofinite,
      (baseChangeAtPrime K L w) (a (primeBelow K L w)) ∈
        ↑(w.adicCompletionIntegers L) := by


  have ha := a.property

  rw [Filter.eventually_cofinite] at ha ⊢


  set S := {v : HeightOneSpectrum (𝓞 K) | a v ∉ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} with hS_def

  apply Set.Finite.subset (s := primeBelow K L ⁻¹' S)
  ·


    have hS_eq : primeBelow K L ⁻¹' S = ⋃ v ∈ S, {w | primeBelow K L w = v} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨primeBelow K L w, h, rfl⟩, fun ⟨v, hv, hvw⟩ => hvw ▸ hv⟩
    rw [hS_eq]
    apply ha.biUnion
    intro v _


    have hinj : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)) :=
      fun a b h => HeightOneSpectrum.ext_iff.mpr h
    apply Set.Finite.subset ((primesOver_finite v.asIdeal (𝓞 L)).preimage hinj.injOn)
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hw ⊢
    refine ⟨w.isPrime, ⟨?_⟩⟩
    show v.asIdeal = Ideal.under (𝓞 K) w.asIdeal
    rw [Ideal.under, ← hw]
    rfl

  ·
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS_def] at hw ⊢


    intro hmem
    exact hw (baseChangeAtPrime_mem_integers K L w _ hmem)

lemma baseChange_commutes (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (k : K) :
    (RestrictedProduct.mk
      (fun w => (baseChangeAtPrime K L w)
        ((algebraMap K (FiniteAdeleRing (𝓞 K) K) k) (primeBelow K L w)))
      (baseChange_restricted_condition K L (algebraMap K (FiniteAdeleRing (𝓞 K) K) k))) =
    algebraMap K (FiniteAdeleRing (𝓞 L) L) k := by
  apply RestrictedProduct.ext; intro w
  simp only [RestrictedProduct.mk_apply]

  have hLHS : ((algebraMap K (FiniteAdeleRing (𝓞 K) K)) k) (primeBelow K L w) =
    (algebraMap K ((primeBelow K L w).adicCompletion K) k) := rfl
  rw [hLHS]

  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp]

  simp only [baseChangeAtPrime, UniformSpace.Completion.extensionHom_coe]

  simp only [localBaseChangeMap, RingHom.comp_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

noncomputable def finAdeleRing_baseChangeHom (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    FiniteAdeleRing (𝓞 K) K →ₐ[K] FiniteAdeleRing (𝓞 L) L where
  toFun a := RestrictedProduct.mk
    (fun w => (baseChangeAtPrime K L w) (a (primeBelow K L w)))
    (baseChange_restricted_condition K L a)
  map_one' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (1 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 1 from rfl, map_one]
    rfl
  map_mul' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a * b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) * b (primeBelow K L w) from rfl, map_mul]
    rfl
  map_zero' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (0 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 0 from rfl, map_zero]
    rfl
  map_add' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a + b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) + b (primeBelow K L w) from rfl, map_add]
    rfl
  commutes' := fun k => baseChange_commutes K L k

def finAdeleRing_includeExt (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    L →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  (Algebra.ofId L (FiniteAdeleRing (𝓞 L) L)).restrictScalars K

def finAdeleRing_tensor_forward (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (FiniteAdeleRing (𝓞 K) K ⊗[K] L) →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (finAdeleRing_baseChangeHom K L)
    (finAdeleRing_includeExt K L) (fun _ _ => Commute.all _ _)

lemma finAdeleRing_tensor_forward_isAlgEquiv
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    ∃ (e : (FiniteAdeleRing (𝓞 K) K ⊗[K] L) ≃ₐ[K] FiniteAdeleRing (𝓞 L) L),
      e.toAlgHom = finAdeleRing_tensor_forward K L :=
  sorry

lemma finAdeleRing_tensor_forward_toRingHom_bijective
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Function.Bijective (finAdeleRing_tensor_forward K L).toRingHom := by
  obtain ⟨e, he⟩ := finAdeleRing_tensor_forward_isAlgEquiv K L
  rw [show (finAdeleRing_tensor_forward K L).toRingHom = e.toAlgHom.toRingHom from by rw [he]]
  exact e.bijective

theorem finAdeleRing_tensor_equiv_of_referenced_results
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    ∃ (e : (FiniteAdeleRing (𝓞 K) K ⊗[K] L) ≃+* FiniteAdeleRing (𝓞 L) L),
      e.toRingHom = (finAdeleRing_tensor_forward K L).toRingHom := by
  have hbij := finAdeleRing_tensor_forward_toRingHom_bijective K L
  exact ⟨RingEquiv.ofBijective _ hbij,
    RingHom.ext fun x => RingEquiv.ofBijective_apply _ hbij x⟩

lemma finAdeleRing_tensor_forward_bijective (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Function.Bijective (finAdeleRing_tensor_forward K L).toRingHom := by
  obtain ⟨e, he⟩ := finAdeleRing_tensor_equiv_of_referenced_results K L
  rw [show (finAdeleRing_tensor_forward K L).toRingHom = e.toRingHom from he.symm]
  exact e.bijective

noncomputable def finiteAdeleRing_tensor_ringEquiv (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (FiniteAdeleRing (𝓞 K) K ⊗[K] L) ≃+* FiniteAdeleRing (𝓞 L) L :=
  RingEquiv.ofBijective (finAdeleRing_tensor_forward K L).toRingHom
    (finAdeleRing_tensor_forward_bijective K L)

theorem finiteAdeleRing_tensor_ringEquiv_compat (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (l : L) : (finiteAdeleRing_tensor_ringEquiv K L)
      (Algebra.TensorProduct.includeRight (R := K) l) =
        algebraMap L (FiniteAdeleRing (𝓞 L) L) l := by
  simp only [finiteAdeleRing_tensor_ringEquiv, RingEquiv.ofBijective_apply]
  show (finAdeleRing_tensor_forward K L) (Algebra.TensorProduct.includeRight l) = _
  have h := Algebra.TensorProduct.lift_comp_includeRight'
    (finAdeleRing_baseChangeHom K L) (finAdeleRing_includeExt K L)
    (fun _ _ => Commute.all _ _)
  rw [finAdeleRing_tensor_forward, ← AlgHom.comp_apply, h]
  simp [finAdeleRing_includeExt, AlgHom.restrictScalars, Algebra.ofId]

theorem finiteAdeleRing_tensor_equiv (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    ∃ (e : (FiniteAdeleRing (𝓞 K) K ⊗[K] L) ≃+* FiniteAdeleRing (𝓞 L) L),
      ∀ (l : L), e (Algebra.TensorProduct.includeRight (R := K) l) =
        algebraMap L (FiniteAdeleRing (𝓞 L) L) l :=
  ⟨finiteAdeleRing_tensor_ringEquiv K L, finiteAdeleRing_tensor_ringEquiv_compat K L⟩

theorem finiteAdeleRing_base_change_iso (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Nonempty ((FiniteAdeleRing (𝓞 K) K ⊗[K] L) ≃+* FiniteAdeleRing (𝓞 L) L) :=
  let ⟨e, _⟩ := finiteAdeleRing_tensor_equiv K L; ⟨e⟩

theorem adeles_base_change (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    letI : Module K (AdeleRing (𝓞 K) K) := (AdeleRing.instAlgebra (𝓞 K) K).toModule
    Nonempty ((AdeleRing (𝓞 L) L) ≃+* ((AdeleRing (𝓞 K) K) ⊗[K] L)) := by
  obtain ⟨e_inf⟩ := infiniteAdeleRing_base_change_iso K L
  obtain ⟨e_fin⟩ := finiteAdeleRing_base_change_iso K L
  haveI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl


  let comm1 := Algebra.TensorProduct.comm K (AdeleRing (𝓞 K) K) L
  let prod1 := Algebra.TensorProduct.prodRight K K L
    (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
  let comm_inf := Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)
  let comm_fin := Algebra.TensorProduct.comm K L (FiniteAdeleRing (𝓞 K) K)

  exact ⟨(RingEquiv.prodCongr e_inf.symm e_fin.symm).trans
    ((RingEquiv.prodCongr comm_inf.symm.toRingEquiv comm_fin.symm.toRingEquiv).trans
      (prod1.symm.toRingEquiv.trans comm1.symm.toRingEquiv))⟩

theorem infiniteAdeleRing_base_change_diagram_aux (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    ∃ (e : TensorProduct K (InfiniteAdeleRing K) L ≃+* InfiniteAdeleRing L),
      ∀ (l : L), e (Algebra.TensorProduct.includeRight (R := K) l) =
        algebraMap L (InfiniteAdeleRing L) l := by
  classical

  obtain ⟨fiber_iso, h_fiber⟩ := completion_tensor_pi_equiv K L

  let comm_alg := Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L
  let pi_alg := Algebra.TensorProduct.piRight K K L
    (fun v : InfinitePlace K => v.Completion)
  let e := comm_alg.toRingEquiv.trans (pi_alg.toRingEquiv.trans fiber_iso)
  refine ⟨e, fun l => ?_⟩

  show fiber_iso (pi_alg (comm_alg (Algebra.TensorProduct.includeRight (R := K) l))) =
    algebraMap L (InfiniteAdeleRing L) l

  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.comm_tmul]

  simp only [pi_alg]

  exact h_fiber l

theorem finiteAdeleRing_base_change_diagram_aux (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    ∃ (e : TensorProduct K (FiniteAdeleRing (𝓞 K) K) L ≃+* FiniteAdeleRing (𝓞 L) L),
      ∀ (l : L), e (Algebra.TensorProduct.includeRight (R := K) l) =
        algebraMap L (FiniteAdeleRing (𝓞 L) L) l :=
  finiteAdeleRing_tensor_equiv K L

theorem adeles_base_change_diagram (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    letI : Module K (AdeleRing (𝓞 K) K) := (AdeleRing.instAlgebra (𝓞 K) K).toModule
    haveI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    ∃ (φ : (AdeleRing (𝓞 L) L) ≃+* ((AdeleRing (𝓞 K) K) ⊗[K] L)),
      ∀ (l : L), φ (algebraMap L (AdeleRing (𝓞 L) L) l) =
        Algebra.TensorProduct.includeRight.toRingHom l := by

  obtain ⟨e_inf, h_inf⟩ := infiniteAdeleRing_base_change_diagram_aux K L
  obtain ⟨e_fin, h_fin⟩ := finiteAdeleRing_base_change_diagram_aux K L
  haveI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl

  let comm1 := Algebra.TensorProduct.comm K (AdeleRing (𝓞 K) K) L
  let prod1 := Algebra.TensorProduct.prodRight K K L
    (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
  let comm_inf := Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)
  let comm_fin := Algebra.TensorProduct.comm K L (FiniteAdeleRing (𝓞 K) K)

  let φ := (RingEquiv.prodCongr e_inf.symm e_fin.symm).trans
    ((RingEquiv.prodCongr comm_inf.symm.toRingEquiv comm_fin.symm.toRingEquiv).trans
      (prod1.symm.toRingEquiv.trans comm1.symm.toRingEquiv))
  refine ⟨φ, fun l => ?_⟩

  show φ (algebraMap L (AdeleRing (𝓞 L) L) l) = Algebra.TensorProduct.includeRight l

  have h1 : e_inf.symm (algebraMap L (InfiniteAdeleRing L) l) =
      Algebra.TensorProduct.includeRight l := by
    rw [RingEquiv.symm_apply_eq]; exact (h_inf l).symm
  have h2 : e_fin.symm (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) =
      Algebra.TensorProduct.includeRight l := by
    rw [RingEquiv.symm_apply_eq]; exact (h_fin l).symm

  simp only [φ, RingEquiv.trans_apply, RingEquiv.prodCongr_apply, Prod.map]

  show comm1.symm.toRingEquiv
    (prod1.symm.toRingEquiv
      (comm_inf.symm.toRingEquiv
          (e_inf.symm (algebraMap L (InfiniteAdeleRing L) l)),
        comm_fin.symm.toRingEquiv
          (e_fin.symm (algebraMap L (FiniteAdeleRing (𝓞 L) L) l)))) =
    Algebra.TensorProduct.includeRight l
  rw [h1, h2]


  simp only [Algebra.TensorProduct.includeRight_apply]


  simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv]

  rw [Algebra.TensorProduct.comm_symm_tmul K l (1 : InfiniteAdeleRing K),
      Algebra.TensorProduct.comm_symm_tmul K l (1 : FiniteAdeleRing (𝓞 K) K)]

  have hp : prod1.symm ((l ⊗ₜ[K] (1 : InfiniteAdeleRing K)),
      (l ⊗ₜ[K] (1 : FiniteAdeleRing (𝓞 K) K))) =
      l ⊗ₜ[K] ((1 : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K)) := by
    rw [AlgEquiv.symm_apply_eq]
    exact Algebra.TensorProduct.prodRight_tmul K K L
      (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) l
      ((1 : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K))
  rw [hp]


  rw [AlgEquiv.symm_apply_eq]


  exact (Algebra.TensorProduct.comm_tmul K
    ((1 : AdeleRing (𝓞 K) K)) l).symm

instance adeleRing_algebra_base (L : Type*) [Field L] [NumberField L]
    [Algebra K L] :
    Algebra K (AdeleRing (𝓞 L) L) :=
  Algebra.compHom (AdeleRing (𝓞 L) L) (algebraMap K L)

omit [NumberField K] in
theorem adeleRing_algebra_base_algebraMap (L : Type*) [Field L] [NumberField L]
    [Algebra K L] :
    algebraMap K (AdeleRing (𝓞 L) L) =
      (algebraMap L (AdeleRing (𝓞 L) L)).comp (algebraMap K L) :=
  rfl

theorem adeles_baseChange_continuous_fwd
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    letI : Module K (AdeleRing (𝓞 K) K) := (AdeleRing.instAlgebra (𝓞 K) K).toModule
    haveI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (φ : AdeleRing (𝓞 L) L ≃+* (AdeleRing (𝓞 K) K ⊗[K] L))
      (b : Module.Basis (Fin (Module.finrank K L)) K L),
      Continuous (fun x : AdeleRing (𝓞 L) L =>
        (Algebra.TensorProduct.equivPiOfFiniteBasis (AdeleRing (𝓞 K) K) b : _ → _) (φ x)) := by
  sorry

theorem adeles_baseChange_continuous_inv
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    let _ : Module K (AdeleRing (𝓞 K) K) := (AdeleRing.instAlgebra (𝓞 K) K).toModule
    ∀ (φ : AdeleRing (𝓞 L) L ≃+* (AdeleRing (𝓞 K) K ⊗[K] L))
      (b : Module.Basis (Fin (Module.finrank K L)) K L),
      Continuous (fun y : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K =>
        φ.symm ((Algebra.TensorProduct.equivPiOfFiniteBasis (AdeleRing (𝓞 K) K) b).symm y)) := by
  intro φ b
  sorry

def adeleRing_directSumDecomposition (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    letI : Module K (AdeleRing (𝓞 L) L) := (adeleRing_algebra_base L).toModule
    AdeleRing (𝓞 L) L ≃L[K] (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) := by
  letI modAL : Module K (AdeleRing (𝓞 L) L) := (adeleRing_algebra_base L).toModule
  letI modAK : Module K (AdeleRing (𝓞 K) K) := (AdeleRing.instAlgebra (𝓞 K) K).toModule
  haveI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl


  have hex := adeles_base_change_diagram (K := K) L
  let φ := hex.choose
  have hφ : ∀ l : L, φ (algebraMap L (AdeleRing (𝓞 L) L) l) =
      Algebra.TensorProduct.includeRight (R := K) (A := AdeleRing (𝓞 K) K) l := by
    intro l; exact hex.choose_spec l
  classical
  letI : Algebra K (TensorProduct K (AdeleRing (𝓞 K) K) L) := Algebra.TensorProduct.instAlgebra

  let step1 : AdeleRing (𝓞 L) L ≃ₗ[K] (TensorProduct K (AdeleRing (𝓞 K) K) L) :=
    φ.toAddEquiv.toLinearEquiv (fun (k : K) (x : AdeleRing (𝓞 L) L) => by
      show φ (k • x) = k • φ x
      rw [Algebra.smul_def (R := K) k x]
      rw [φ.map_mul]
      rw [show φ (algebraMap K (AdeleRing (𝓞 L) L) k) =
          Algebra.TensorProduct.includeRight (R := K) (A := AdeleRing (𝓞 K) K)
            (algebraMap K L k) from hφ _]
      have hcomm : (Algebra.TensorProduct.includeRight (R := K)
            (A := AdeleRing (𝓞 K) K) : L →ₐ[K] _).toRingHom (algebraMap K L k) =
          algebraMap K (TensorProduct K (AdeleRing (𝓞 K) K) L) k :=
        AlgHom.commutes _ k
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hcomm
      rw [hcomm]
      exact (Algebra.smul_def k (φ x)).symm)

  let b := Module.finBasis K L
  let step2 := (Algebra.TensorProduct.equivPiOfFiniteBasis
    (AdeleRing (𝓞 K) K) b).restrictScalars K
  let e := step1.trans step2


  have h_fwd_cont : Continuous ⇑e := by
    have := adeles_baseChange_continuous_fwd (K := K) L φ b
    convert this using 1
  have h_inv_cont : Continuous ⇑e.symm := by
    have := adeles_baseChange_continuous_inv (K := K) L φ b
    convert this using 1
  exact { toLinearEquiv := e, continuous_toFun := h_fwd_cont, continuous_invFun := h_inv_cont }

theorem adeleRing_directSumDecomposition_principalRestriction (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    let φ := adeleRing_directSumDecomposition L (K := K)
    let b := Module.finBasis K L
    ∀ (l : L), φ (algebraMap L (AdeleRing (𝓞 L) L) l) =
      fun i => algebraMap K (AdeleRing (𝓞 K) K) (b.equivFun l i) := by
  intro φ b l
  simp only [φ]
  letI : Module K (AdeleRing (𝓞 L) L) := (adeleRing_algebra_base L).toModule
  haveI : IsScalarTower K K L := IsScalarTower.of_algebraMap_eq' rfl


  have hex := adeles_base_change_diagram (K := K) L
  have hψ := hex.choose_spec


  ext i


  change (adeleRing_directSumDecomposition L (K := K)).toLinearEquiv ((algebraMap L (AdeleRing (𝓞 L) L)) l) i =
    (algebraMap K (AdeleRing (𝓞 K) K)) (b.equivFun l i)


  unfold adeleRing_directSumDecomposition
  simp only [LinearEquiv.trans_apply]


  erw [hψ l]

  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Algebra.TensorProduct.includeRight_apply]


  show (Algebra.TensorProduct.equivPiOfFiniteBasis (AdeleRing (𝓞 K) K) (Module.finBasis K L))
      (1 ⊗ₜ[K] l) i = (algebraMap K (AdeleRing (𝓞 K) K)) ((Module.finBasis K L).equivFun l i)
  simp only [Algebra.TensorProduct.equivPiOfFiniteBasis_apply,
    LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul]
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

def adelicBox (a : adeleRing (K := K)) : Set (adeleRing (K := K)) :=
  { t | (∀ v : HeightOneSpectrum (𝓞 K), ‖t.2 v‖ ≤ ‖a.2 v‖) ∧
        (∀ w : InfinitePlace K, ‖t.1 w‖ ≤ ‖a.1 w‖ / 4) }

theorem haar_blichfeldt_pigeonhole_axiom (K : Type*) [Field K] [NumberField K]
    (a : adeleRing (K := K)) (ha : adelicAbsVal a > 0) :
    ∃ (s₁ s₂ : adeleRing (K := K)),
      s₁ ∈ adelicBox a ∧ s₂ ∈ adelicBox a ∧ s₁ ≠ s₂ ∧
      (s₁ - s₂) ∈ (principalSubgroup (K := K) : Set (adeleRing (K := K))) := by
  sorry

theorem adeleRing_adelicBox_blichfeldt (K : Type*) [Field K] [NumberField K]
    (a : adeleRing (K := K)) (ha : adelicAbsVal a > 0) :
    ∃ (s₁ s₂ : adeleRing (K := K)),
      s₁ ∈ adelicBox a ∧ s₂ ∈ adelicBox a ∧ s₁ ≠ s₂ ∧
      ∃ c : K, s₁ - s₂ = algebraMap K (adeleRing (K := K)) c := by
  obtain ⟨s₁, s₂, hs₁, hs₂, hne, hmem⟩ := haar_blichfeldt_pigeonhole_axiom K a ha
  refine ⟨s₁, s₂, hs₁, hs₂, hne, ?_⟩

  have hmem' : s₁ - s₂ ∈ (algebraMap K (adeleRing (K := K))).range.toAddSubgroup := hmem
  rw [Subring.mem_toAddSubgroup] at hmem'
  obtain ⟨c, hc⟩ := hmem'
  exact ⟨c, hc.symm⟩

lemma adelicBox_blichfeldt_pigeonhole (K : Type*) [Field K] [NumberField K]
    (b₀ b₁ : ℝ) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (a : adeleRing (K := K)) (ha : b₁ * adelicAbsVal a > b₀) :
    ∃ (s₁ s₂ : adeleRing (K := K)),
      s₁ ∈ adelicBox a ∧ s₂ ∈ adelicBox a ∧ s₁ ≠ s₂ ∧
      ∃ c : K, s₁ - s₂ = algebraMap K (adeleRing (K := K)) c := by

  have ha_pos : adelicAbsVal a > 0 := by
    by_contra h
    push Not at h
    have : b₁ * adelicAbsVal a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb₁) h
    linarith

  exact adeleRing_adelicBox_blichfeldt K a ha_pos

lemma adelic_blichfeldt_pigeonhole_aux (K : Type*) [Field K] [NumberField K] :
    ∃ (b₀ b₁ : ℝ), 0 < b₀ ∧ 0 < b₁ ∧
    ∀ (a : adeleRing (K := K)),
      b₁ * adelicAbsVal a > b₀ →
      ∃ (s₁ s₂ : adeleRing (K := K)),
        s₁ ∈ adelicBox a ∧ s₂ ∈ adelicBox a ∧ s₁ ≠ s₂ ∧
        ∃ c : K, s₁ - s₂ = algebraMap K (adeleRing (K := K)) c := by
  exact ⟨1, 1, one_pos, one_pos,
    fun a ha => adelicBox_blichfeldt_pigeonhole K 1 1 one_pos one_pos a ha⟩

theorem exists_pair_in_box_with_nonzero_diff (K : Type*) [Field K] [NumberField K] :
    ∃ (b₀ b₁ : ℝ), 0 < b₀ ∧ 0 < b₁ ∧
    ∀ (a : adeleRing (K := K)),
      b₁ * adelicAbsVal a > b₀ →
      ∃ (s₁ s₂ : adeleRing (K := K)) (c : K),
        s₁ ∈ adelicBox a ∧ s₂ ∈ adelicBox a ∧ c ≠ 0 ∧
        s₁ - s₂ = algebraMap K (adeleRing (K := K)) c := by
  obtain ⟨b₀, b₁, hb₀, hb₁, hpigeonhole⟩ := adelic_blichfeldt_pigeonhole_aux K
  refine ⟨b₀, b₁, hb₀, hb₁, fun a ha => ?_⟩
  obtain ⟨s₁, s₂, hs₁, hs₂, hne, c, hc⟩ := hpigeonhole a ha
  refine ⟨s₁, s₂, c, hs₁, hs₂, ?_, hc⟩


  intro hc0
  exact hne (sub_eq_zero.mp (by rw [hc, hc0, map_zero]))

theorem haar_blichfeldt_constants (K : Type*) [Field K] [NumberField K] :
    ∃ (b₀ b₁ : ℝ), 0 < b₀ ∧ 0 < b₁ ∧
    ∀ (a : adeleRing (K := K)),
      b₁ * adelicAbsVal a > b₀ →
      ∃ (x y : K), x ≠ y ∧
        ((fun s => algebraMap K (adeleRing (K := K)) x + s) '' (adelicBox a) ∩
         (fun s => algebraMap K (adeleRing (K := K)) y + s) '' (adelicBox a)).Nonempty := by
  obtain ⟨b₀, b₁, hb₀, hb₁, hbox⟩ := exists_pair_in_box_with_nonzero_diff K
  refine ⟨b₀, b₁, hb₀, hb₁, fun a ha => ?_⟩
  obtain ⟨s₁, s₂, c, hs₁, hs₂, hc_ne, hs⟩ := hbox a ha


  refine ⟨0, c, fun h => hc_ne h.symm, ?_⟩
  refine ⟨s₁, ?_, ?_⟩
  ·
    rw [Set.mem_image]
    exact ⟨s₁, hs₁, by simp [map_zero]⟩
  ·
    rw [Set.mem_image]
    exact ⟨s₂, hs₂, (eq_add_of_sub_eq hs).symm⟩

theorem adelic_box_translates_overlap (K : Type*) [Field K] [NumberField K] :
    ∃ B : ℝ, 0 < B ∧
    ∀ (a : adeleRing (K := K)), adelicAbsVal a > B →
    ∃ (x y : K), x ≠ y ∧
      ((fun s => algebraMap K (adeleRing (K := K)) x + s) '' (adelicBox a) ∩
       (fun s => algebraMap K (adeleRing (K := K)) y + s) '' (adelicBox a)).Nonempty := by

  obtain ⟨b₀, b₁, hb₀, hb₁, hblichfeldt⟩ := haar_blichfeldt_constants K

  refine ⟨b₀ / b₁, div_pos hb₀ hb₁, fun a ha => ?_⟩

  have hmeasure : b₁ * adelicAbsVal a > b₀ := by
    calc b₁ * adelicAbsVal a
        > b₁ * (b₀ / b₁) := mul_lt_mul_of_pos_left ha hb₁
      _ = b₀ := by field_simp

  exact hblichfeldt a hmeasure

theorem adelic_blichfeldt_for_box :
    ∃ B : ℝ, 0 < B ∧
    ∀ (a : adeleRing (K := K)), adelicAbsVal a > B →
    ∃ t₁ ∈ adelicBox a, ∃ t₂ ∈ adelicBox a,
      t₁ ≠ t₂ ∧ (t₁ - t₂) ∈ Set.range (algebraMap K (adeleRing (K := K))) := by


  obtain ⟨B, hB, haxiom⟩ := adelic_box_translates_overlap K
  refine ⟨B, hB, fun a ha => ?_⟩
  obtain ⟨x, y, hxy, z, hz⟩ := haxiom a ha

  simp only [Set.mem_inter_iff, Set.mem_image] at hz
  obtain ⟨⟨t₁, ht₁, hzt₁⟩, ⟨t₂, ht₂, hzt₂⟩⟩ := hz
  refine ⟨t₁, ht₁, t₂, ht₂, ?_, ?_⟩
  ·
    intro heq
    apply hxy
    apply diag_injective (K := K)
    have h : algebraMap K (adeleRing (K := K)) x + t₁ =
             algebraMap K (adeleRing (K := K)) y + t₁ := by
      calc algebraMap K (adeleRing (K := K)) x + t₁
          = z := hzt₁
        _ = algebraMap K (adeleRing (K := K)) y + t₂ := hzt₂.symm
        _ = algebraMap K (adeleRing (K := K)) y + t₁ := by rw [heq]
    exact add_right_cancel h
  ·
    refine ⟨y - x, ?_⟩
    have h1 : t₁ = z - algebraMap K (adeleRing (K := K)) x := by
      rw [← hzt₁]; ring
    have h2 : t₂ = z - algebraMap K (adeleRing (K := K)) y := by
      rw [← hzt₂]; ring
    rw [h1, h2, map_sub]; ring

theorem adelic_pigeonhole_haar :
    ∃ B : ℝ, 0 < B ∧
      ∀ (a : adeleRing (K := K)),
        adelicAbsVal a > B →
        ∃ (t₁ t₂ : adeleRing (K := K)),
          t₁ ≠ t₂ ∧
          (∀ v : HeightOneSpectrum (𝓞 K), ‖t₁.2 v‖ ≤ ‖a.2 v‖) ∧
          (∀ v : HeightOneSpectrum (𝓞 K), ‖t₂.2 v‖ ≤ ‖a.2 v‖) ∧
          (∀ w : InfinitePlace K, ‖t₁.1 w‖ ≤ ‖a.1 w‖ / 4) ∧
          (∀ w : InfinitePlace K, ‖t₂.1 w‖ ≤ ‖a.1 w‖ / 4) ∧
          (t₁ - t₂) ∈ Set.range (algebraMap K (adeleRing (K := K))) := by
  obtain ⟨B, hB, hbox⟩ := adelic_blichfeldt_for_box (K := K)
  refine ⟨B, hB, fun a ha => ?_⟩
  obtain ⟨t₁, ⟨hfin1, hinf1⟩, t₂, ⟨hfin2, hinf2⟩, hne, hK⟩ := hbox a ha
  exact ⟨t₁, t₂, hne, hfin1, hfin2, hinf1, hinf2, hK⟩

theorem adelic_blichfeldt_minkowski :
    ∃ B : ℝ, 0 < B ∧
      ∀ (a : adeleRing (K := K)),
        adelicAbsVal a > B →
        ∃ (x : K), x ≠ 0 ∧
          ∀ (v : Place K), placeNormAdele v (algebraMap K (adeleRing (K := K)) x) ≤
            placeNormAdele v a := by
  obtain ⟨B, hB, hpigeonhole⟩ := adelic_pigeonhole_haar (K := K)
  refine ⟨B, hB, fun a ha => ?_⟩
  obtain ⟨t₁, t₂, hne, hfin1, hfin2, hinf1, hinf2, x, hx⟩ := hpigeonhole a ha
  refine ⟨x, ?_, fun v => ?_⟩
  ·
    intro hx0; apply hne
    have h0 : algebraMap K (adeleRing (K := K)) x = 0 := by rw [hx0, map_zero]
    rw [hx] at h0; exact sub_eq_zero.mp h0
  ·
    rw [hx]
    match v with
    | .finite vi =>

      show ‖(t₁ - t₂).2 vi‖ ≤ ‖a.2 vi‖
      calc ‖(t₁ - t₂).2 vi‖ = ‖t₁.2 vi - t₂.2 vi‖ := rfl
        _ = ‖t₁.2 vi + (-(t₂.2 vi))‖ := by rw [sub_eq_add_neg]
        _ ≤ max ‖t₁.2 vi‖ ‖-(t₂.2 vi)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖t₁.2 vi‖ ‖t₂.2 vi‖ := by rw [norm_neg]
        _ ≤ ‖a.2 vi‖ := max_le (hfin1 vi) (hfin2 vi)
    | .infinite w =>

      show ‖(t₁ - t₂).1 w‖ ≤ ‖a.1 w‖
      calc ‖(t₁ - t₂).1 w‖ = ‖t₁.1 w - t₂.1 w‖ := rfl
        _ ≤ ‖t₁.1 w‖ + ‖t₂.1 w‖ := norm_sub_le _ _
        _ ≤ ‖a.1 w‖ / 4 + ‖a.1 w‖ / 4 := add_le_add (hinf1 w) (hinf2 w)
        _ ≤ ‖a.1 w‖ := by linarith [norm_nonneg (a.1 w)]

instance instNormOneClass_Completion (w : InfinitePlace K) : NormOneClass w.Completion where
  norm_one := by
    have : (1 : w.Completion) = algebraMap K w.Completion 1 := (map_one _).symm
    rw [this, show algebraMap K w.Completion 1 =
      (↑((WithAbs.equiv w.1).symm 1) : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe]; simp

instance instNontrivNormedField_InfCompl (w : InfinitePlace K) :
    NontriviallyNormedField w.Completion := by
  refine { InfinitePlace.Completion.instNormedField w with non_trivial := ?_ }
  use algebraMap K w.Completion 2
  rw [show algebraMap K w.Completion 2 =
    (↑((WithAbs.equiv w.1).symm 2) : w.Completion) from rfl]
  rw [InfinitePlace.Completion.norm_coe]
  show 1 < w 2
  rw [(w.norm_embedding_eq 2).symm]; simp only [map_ofNat]; norm_num

lemma mem_adicCompletionIntegers_iff_norm_le_one (vi : HeightOneSpectrum (𝓞 K))
    (x : vi.adicCompletion K) :
    x ∈ vi.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valued.toNormedField.norm_le_one_iff (L := vi.adicCompletion K)
    (Γ₀ := WithZero (Multiplicative ℤ))).symm

theorem exists_strategic_adele
    (B : ℝ) (hB : 0 < B)
    (S : Finset (Place K)) (w : Place K) (hw : w ∉ S)
    (ε : (v : Place K) → v ∈ S → ℝ) (hε : ∀ v (hv : v ∈ S), 0 < ε v hv) :
    ∃ (z : adeleRing (K := K)),
      adelicAbsVal z > B ∧
      (∀ v (hv : v ∈ S), placeNormAdele v z ≤ ε v hv) ∧
      (∀ v : Place K, v ∉ S → v ≠ w → placeNormAdele v z ≤ 1) ∧
      (Function.mulSupport
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => ‖z.2 v‖)).Finite := by
  classical
  rcases w with ⟨vi_w⟩ | ⟨w_inf⟩
  ·


    let inf_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        Classical.choose (NormedField.exists_norm_lt w'.Completion (hε _ hS))
      else 1

    let S_fin := S.preimage Place.finite (fun a _ b _ h => Place.finite.inj h)
    let s_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        Classical.choose (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hS) one_pos))
      else 1


    let P_inf : ℝ := ∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult
    have hP_inf_pos : 0 < P_inf := by
      apply Finset.prod_pos
      intro w' _
      apply pow_pos
      simp only [inf_fn]
      split_ifs with hS
      · exact (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hS))).1
      · simp [norm_one]

    let P_fin : ℝ := ∏ vi ∈ S_fin, ‖s_fn vi‖
    have hP_fin_pos : 0 < P_fin := by
      apply Finset.prod_pos
      intro vi hvi
      simp only [S_fin, Finset.mem_preimage] at hvi
      simp only [s_fn, dif_pos hvi]
      letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
        (WithZero (Multiplicative ℤ))
      exact (Classical.choose_spec
        (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hvi) one_pos))).1
    let P : ℝ := P_inf * P_fin
    have hP_pos : 0 < P := mul_pos hP_inf_pos hP_fin_pos

    letI := Valued.toNontriviallyNormedField (vi_w.adicCompletion K)
      (WithZero (Multiplicative ℤ))
    let vi_w_elem := Classical.choose
      (NormedField.exists_lt_norm (vi_w.adicCompletion K) ((B + 1) / P))
    have hw_spec : (B + 1) / P < ‖vi_w_elem‖ :=
      Classical.choose_spec
        (NormedField.exists_lt_norm (vi_w.adicCompletion K) ((B + 1) / P))

    let fin_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then s_fn vi
      else if h : vi = vi_w then h ▸ vi_w_elem
      else 1


    have fin_mem : ∀ᶠ vi in Filter.cofinite,
        fin_fn vi ∈ vi.adicCompletionIntegers K := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset
      · exact (S_fin.finite_toSet).union (Set.finite_singleton vi_w)
      · intro vi hvi
        simp only [Set.mem_setOf_eq] at hvi
        by_contra h_not
        simp only [Set.mem_union, Finset.mem_coe, S_fin, Finset.mem_preimage,
          Set.mem_singleton_iff] at h_not
        push Not at h_not
        have h1 : ¬ Place.finite vi ∈ S := h_not.1
        have h2 : ¬ vi = vi_w := h_not.2
        simp only [fin_fn, dif_neg h1, dif_neg h2] at hvi
        exact hvi ((vi.adicCompletionIntegers K).one_mem')
    let z : adeleRing (K := K) := (inf_fn, RestrictedProduct.mk fin_fn fin_mem)
    refine ⟨z, ?_, ?_, ?_, ?_⟩

    ·


      unfold adelicAbsVal
      simp only [z]

      have hinf_eq : ∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult = P_inf := rfl


      let g : HeightOneSpectrum (𝓞 K) → ℝ := fun vi => ‖fin_fn vi‖

      have hsupp : Function.mulSupport g ⊆ ↑(S_fin ∪ {vi_w}) := by
        intro vi hvi
        simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
          S_fin, Finset.mem_preimage, Set.mem_singleton_iff]
        by_contra h_not
        push Not at h_not
        have h1 : ¬ Place.finite vi ∈ S := h_not.1
        have h2 : ¬ vi = vi_w := h_not.2
        simp only [g, fin_fn, dif_neg h1, dif_neg h2, norm_one] at hvi
        exact hvi rfl

      have hfin_eq : ∏ᶠ vi, g vi = ∏ vi ∈ S_fin ∪ {vi_w}, g vi :=
        finprod_eq_prod_of_mulSupport_subset g hsupp

      have hvi_w_notin : vi_w ∉ S_fin := by
        simp only [S_fin, Finset.mem_preimage]
        exact hw

      have hsplit : ∏ vi ∈ S_fin ∪ {vi_w}, g vi =
          (∏ vi ∈ S_fin, g vi) * (∏ vi ∈ ({vi_w} : Finset _), g vi) :=
        Finset.prod_union (Finset.disjoint_singleton_right.mpr hvi_w_notin)

      have hsingleton : ∏ vi ∈ ({vi_w} : Finset _), g vi = ‖vi_w_elem‖ := by
        simp only [Finset.prod_singleton, g, fin_fn, dif_neg hw, dite_true]

      have hS_prod : ∏ vi ∈ S_fin, g vi = P_fin := by
        apply Finset.prod_congr rfl
        intro vi hvi
        simp only [S_fin, Finset.mem_preimage] at hvi
        simp only [g, fin_fn, dif_pos hvi]


      have hfinprod_val : ∏ᶠ vi, g vi = P_fin * ‖vi_w_elem‖ := by
        rw [hfin_eq, hsplit, hS_prod, hsingleton]

      have hmk : ∀ vi, ‖(RestrictedProduct.mk fin_fn fin_mem) vi‖ = g vi := by
        intro vi; simp [g, RestrictedProduct.mk_apply]

      have hfp_eq : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
          ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) = P_fin * ‖vi_w_elem‖ := by
        trans (∏ᶠ vi, g vi)
        · exact finprod_congr hmk
        · exact hfinprod_val

      have hbound : P_inf * (P_fin * ‖vi_w_elem‖) > B := by
        calc B < B + 1 := by linarith
          _ = (B + 1) / P * P := by rw [div_mul_cancel₀]; exact ne_of_gt hP_pos
          _ < ‖vi_w_elem‖ * P := mul_lt_mul_of_pos_right hw_spec hP_pos
          _ = ‖vi_w_elem‖ * (P_inf * P_fin) := rfl
          _ = P_inf * (P_fin * ‖vi_w_elem‖) := by ring
      have hgoal_eq : (∏ x : InfinitePlace K, ‖inf_fn x‖ ^ x.mult) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
            ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) =
          P_inf * (P_fin * ‖vi_w_elem‖) := by
        rw [hinf_eq]; congr 1
      exact hgoal_eq ▸ hbound
    ·
      intro v hv
      match v, hv with
      | .infinite w', hv =>
        show ‖inf_fn w'‖ ≤ ε (Place.infinite w') hv
        simp only [inf_fn, dif_pos hv]
        exact le_of_lt (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hv))).2
      | .finite vi, hv =>
        show ‖fin_fn vi‖ ≤ ε (Place.finite vi) hv
        simp only [fin_fn, s_fn, dif_pos hv]
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        have spec := Classical.choose_spec (NormedField.exists_norm_lt
          (vi.adicCompletion K) (lt_min (hε (.finite vi) hv) one_pos))
        exact le_of_lt (lt_of_lt_of_le spec.2 (min_le_left _ _))
    ·
      intro v hvS hne
      match v, hvS, hne with
      | .infinite w', hvS, _ =>
        show ‖inf_fn w'‖ ≤ 1
        simp only [inf_fn, dif_neg hvS, norm_one, le_refl]
      | .finite vi, hvS, hne =>
        show ‖fin_fn vi‖ ≤ 1
        have hnotW : vi ≠ vi_w := fun h => hne (congrArg Place.finite h)
        simp only [fin_fn, dif_neg hvS, dif_neg hnotW, norm_one, le_refl]
    ·
      apply Set.Finite.subset ((S_fin ∪ {vi_w}).finite_toSet)
      intro vi hvi
      simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
      change ‖fin_fn vi‖ ≠ 1 at hvi
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
        S_fin, Finset.mem_preimage, Set.mem_singleton_iff]
      by_contra h_not
      push Not at h_not
      have h1 : ¬ Place.finite vi ∈ S := h_not.1
      have h2 : ¬ vi = vi_w := h_not.2
      simp only [fin_fn, dif_neg h1, dif_neg h2, norm_one] at hvi
      exact hvi rfl

  ·

    let inf_S_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        Classical.choose (NormedField.exists_norm_lt w'.Completion (hε _ hS))
      else 1
    let S_fin := S.preimage Place.finite (fun a _ b _ h => Place.finite.inj h)
    let fin_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K) (WithZero (Multiplicative ℤ))
        Classical.choose (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hS) one_pos))
      else 1

    let P_inf_other : ℝ := ∏ w' : InfinitePlace K, ‖inf_S_fn w'‖ ^ w'.mult
    have hP_inf_other_pos : 0 < P_inf_other := by
      apply Finset.prod_pos; intro w' _; apply pow_pos
      simp only [inf_S_fn]; split_ifs with hS
      · exact (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hS))).1
      · simp [norm_one]
    let P_fin : ℝ := ∏ vi ∈ S_fin, ‖fin_fn vi‖
    have hP_fin_pos : 0 < P_fin := by
      apply Finset.prod_pos; intro vi hvi
      simp only [S_fin, Finset.mem_preimage] at hvi
      simp only [fin_fn, dif_pos hvi]
      letI := Valued.toNontriviallyNormedField (vi.adicCompletion K) (WithZero (Multiplicative ℤ))
      exact (Classical.choose_spec (NormedField.exists_norm_lt (vi.adicCompletion K)
        (lt_min (hε (.finite vi) hvi) one_pos))).1
    let P : ℝ := P_inf_other * P_fin
    have hP_pos : 0 < P := mul_pos hP_inf_other_pos hP_fin_pos

    let w_inf_elem := Classical.choose
      (NormedField.exists_lt_norm w_inf.Completion ((B + 1) / P + 1))
    have hw_spec : (B + 1) / P + 1 < ‖w_inf_elem‖ :=
      Classical.choose_spec (NormedField.exists_lt_norm w_inf.Completion ((B + 1) / P + 1))
    have hw_gt_one : 1 < ‖w_inf_elem‖ := by
      calc 1 ≤ (B + 1) / P + 1 := le_add_of_nonneg_left (div_nonneg (by linarith) (le_of_lt hP_pos))
        _ < ‖w_inf_elem‖ := hw_spec
    have hw_norm_pos : 0 < ‖w_inf_elem‖ := by linarith

    let inf_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        inf_S_fn w'
      else if h : w' = w_inf then h ▸ w_inf_elem
      else 1

    have fin_mem : ∀ᶠ vi in Filter.cofinite,
        fin_fn vi ∈ vi.adicCompletionIntegers K := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset
      · exact (S.preimage Place.finite
            (fun a _ b _ h => Place.finite.inj h)).finite_toSet
      · intro vi hvi
        simp only [Set.mem_setOf_eq] at hvi
        by_contra h_not
        simp only [Finset.mem_coe, Finset.mem_preimage] at h_not
        simp only [fin_fn, dif_neg h_not] at hvi
        exact hvi ((vi.adicCompletionIntegers K).one_mem')
    let z : adeleRing (K := K) := (inf_fn, RestrictedProduct.mk fin_fn fin_mem)
    refine ⟨z, ?_, ?_, ?_, ?_⟩

    ·
      unfold adelicAbsVal
      simp only [z]


      have hinf_S : ∀ w' : InfinitePlace K, w' ≠ w_inf →
          ‖inf_fn w'‖ = ‖inf_S_fn w'‖ := by
        intro w' hw'
        simp only [inf_fn]
        rw [dite_eq_ite]
        split_ifs with hS
        · simp only [inf_S_fn, dif_pos hS]
        · simp only [inf_S_fn, dif_neg (show ¬ Place.infinite w' ∈ S from by
            intro hc; exact hS hc), norm_one]
      have hinf_w : ‖inf_fn w_inf‖ = ‖w_inf_elem‖ := by
        simp only [inf_fn, dif_neg hw, dite_true]

      let g : HeightOneSpectrum (𝓞 K) → ℝ := fun vi => ‖fin_fn vi‖
      have hsupp : Function.mulSupport g ⊆ ↑S_fin := by
        intro vi hvi
        simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
        simp only [Finset.mem_coe, S_fin, Finset.mem_preimage]
        by_contra h_not
        simp only [g, fin_fn, dif_neg h_not, norm_one] at hvi
        exact hvi rfl
      have hfin_eq : ∏ᶠ vi, g vi = ∏ vi ∈ S_fin, g vi :=
        finprod_eq_prod_of_mulSupport_subset g hsupp
      have hS_prod : ∏ vi ∈ S_fin, g vi = P_fin := by
        apply Finset.prod_congr rfl; intro vi hvi
        simp only [S_fin, Finset.mem_preimage] at hvi
        simp only [g, fin_fn, dif_pos hvi]
      have hfinprod_val : ∏ᶠ vi, g vi = P_fin := by
        rw [hfin_eq, hS_prod]
      have hmk : ∀ vi, ‖(RestrictedProduct.mk fin_fn fin_mem) vi‖ = g vi := by
        intro vi; simp [g, RestrictedProduct.mk_apply]
      have hfp_eq : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
          ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) = P_fin := by
        trans (∏ᶠ vi, g vi)
        · exact finprod_congr hmk
        · exact hfinprod_val


      have hinf_S_at_w : ‖inf_S_fn w_inf‖ = 1 := by
        simp only [inf_S_fn, dif_neg hw, norm_one]
      have hinf_prod_eq : (∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult) =
          P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult := by

        have hmem : w_inf ∈ Finset.univ := Finset.mem_univ w_inf

        rw [← Finset.mul_prod_erase _ _ hmem]

        rw [hinf_w]

        have hlhs : ∏ x ∈ Finset.univ.erase w_inf, ‖inf_fn x‖ ^ x.mult =
            ∏ x ∈ Finset.univ.erase w_inf, ‖inf_S_fn x‖ ^ x.mult := by
          apply Finset.prod_congr rfl
          intro w' hw'
          rw [Finset.mem_erase] at hw'
          rw [hinf_S w' hw'.1]
        rw [hlhs]


        have hP_factor : P_inf_other =
            (fun w' => ‖inf_S_fn w'‖ ^ w'.mult) w_inf *
            ∏ x ∈ Finset.univ.erase w_inf, (fun w' => ‖inf_S_fn w'‖ ^ w'.mult) x :=
          (Finset.mul_prod_erase _ _ hmem).symm
        simp only at hP_factor
        rw [hP_factor, hinf_S_at_w, one_pow, one_mul]
        ring
      have hbound : P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin > B := by
        have h_mult_pos : 0 < w_inf.mult := w_inf.mult_pos
        have hpow_ge : ‖w_inf_elem‖ ^ w_inf.mult ≥ ‖w_inf_elem‖ :=
          le_self_pow₀ (le_of_lt hw_gt_one) h_mult_pos.ne'
        calc B < B + 1 := by linarith
          _ = (B + 1) / P * P := by rw [div_mul_cancel₀]; exact ne_of_gt hP_pos
          _ < ((B + 1) / P + 1) * P := by nlinarith
          _ < ‖w_inf_elem‖ * P := mul_lt_mul_of_pos_right hw_spec hP_pos
          _ = ‖w_inf_elem‖ * (P_inf_other * P_fin) := rfl
          _ ≤ ‖w_inf_elem‖ ^ w_inf.mult * (P_inf_other * P_fin) := by
              exact mul_le_mul_of_nonneg_right hpow_ge (le_of_lt hP_pos)
          _ = P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin := by ring
      have hgoal_eq : (∏ x : InfinitePlace K, ‖inf_fn x‖ ^ x.mult) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
            ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) =
          P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin := by
        rw [hinf_prod_eq]; ring_nf; rw [hfp_eq]
      exact hgoal_eq ▸ hbound
    ·
      intro v hv
      match v, hv with
      | .infinite w', hv =>
        show ‖inf_fn w'‖ ≤ ε (Place.infinite w') hv
        simp only [inf_fn, inf_S_fn, dif_pos hv]
        exact le_of_lt (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hv))).2
      | .finite vi, hv =>
        show ‖fin_fn vi‖ ≤ ε (Place.finite vi) hv
        simp only [fin_fn, dif_pos hv]
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        have spec := Classical.choose_spec (NormedField.exists_norm_lt
          (vi.adicCompletion K) (lt_min (hε (.finite vi) hv) one_pos))
        exact le_of_lt (lt_of_lt_of_le spec.2 (min_le_left _ _))
    ·
      intro v hvS hne
      match v, hvS, hne with
      | .infinite w', hvS, hne =>
        show ‖inf_fn w'‖ ≤ 1
        have hnotW : w' ≠ w_inf := fun h => hne (congrArg Place.infinite h)
        simp only [inf_fn, dif_neg hvS, dif_neg hnotW, norm_one, le_refl]
      | .finite vi, hvS, _ =>
        show ‖fin_fn vi‖ ≤ 1
        simp only [fin_fn, dif_neg hvS, norm_one, le_refl]
    ·
      apply Set.Finite.subset (S_fin.finite_toSet)
      intro vi hvi
      simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
      change ‖fin_fn vi‖ ≠ 1 at hvi
      simp only [Finset.mem_coe, S_fin, Finset.mem_preimage]
      by_contra h_not
      simp only [fin_fn, dif_neg h_not, norm_one] at hvi
      exact hvi rfl

theorem exists_element_with_controlled_norms
    (S : Finset (Place K)) (w : Place K) (hw : w ∉ S)
    (ε : (v : Place K) → v ∈ S → ℝ) (hε : ∀ v (hv : v ∈ S), 0 < ε v hv) :
    ∃ (u : K), u ≠ 0 ∧
      (∀ v (hv : v ∈ S), placeNorm v u ≤ ε v hv) ∧
      (∀ v : Place K, v ∉ S → v ≠ w → placeNorm v u ≤ 1) := by

  obtain ⟨B, hB_pos, hBM⟩ := adelic_blichfeldt_minkowski (K := K)

  obtain ⟨z, hz_large, hz_S, hz_T, -⟩ := exists_strategic_adele B hB_pos S w hw ε hε


  obtain ⟨u, hu_ne, hu_bound⟩ := hBM z hz_large

  refine ⟨u, hu_ne, ?_, ?_⟩
  ·
    intro v hv
    rw [placeNorm_eq_placeNormAdele_algebraMap]
    exact le_trans (hu_bound v) (hz_S v hv)
  ·
    intro v hv_notin_S hv_ne_w
    rw [placeNorm_eq_placeNormAdele_algebraMap]
    exact le_trans (hu_bound v) (hz_T v hv_notin_S hv_ne_w)

lemma adicAbv_le_one_of_mem_integers_algebraMap (vi : HeightOneSpectrum (𝓞 K)) (x : K)
    (hx : algebraMap K (vi.adicCompletion K) x ∈
      (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))) :
    NumberField.HeightOneSpectrum.adicAbv K vi x ≤ 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def]
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K)] at hx
  have : algebraMap K (vi.adicCompletion K) x = (x : vi.adicCompletion K) := rfl
  rw [this] at hx
  rw [vi.valuedAdicCompletion_eq_valuation' x] at hx
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal vi)).mpr hx

omit [NumberField K] in
lemma placeNorm_infinite_eq_norm_algebraMap (w : InfinitePlace K) (x : K) :
    w x = ‖algebraMap K w.Completion x‖ := by
  rw [show algebraMap K w.Completion x =
    (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
  rw [InfinitePlace.Completion.norm_coe]; simp

theorem adeles_K_plus_unit_ball
    (S : Finset (Place K)) (a : (v : Place K) → v ∈ S → K) :
    ∃ (c : K),
      (∀ v (hv : v ∈ S), placeNorm v (c - a v hv) ≤ coveringBound K) ∧
      (∀ v : Place K, v ∉ S → placeNorm v c ≤ coveringBound K) := by

  let finPartFun : ∀ vi : HeightOneSpectrum (𝓞 K), vi.adicCompletion K := fun vi =>
    if h : Place.finite vi ∈ S
    then algebraMap K (vi.adicCompletion K) (a (.finite vi) h)
    else 0
  have hfin_mem : ∀ᶠ vi in Filter.cofinite,
      finPartFun vi ∈ (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) := by
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.Finite.preimage
      (fun v₁ _ v₂ _ h => Place.finite.inj h) S.finite_toSet)
    intro vi hvi
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe] at *
    by_contra hmem
    exact hvi (by simp only [finPartFun, dif_neg hmem]; exact (vi.adicCompletionIntegers K).zero_mem)
  let b : adeleRing (K := K) :=
    ((fun w => if h : Place.infinite w ∈ S
      then algebraMap K w.Completion (a (.infinite w) h) else 0),
     ⟨finPartFun, hfin_mem⟩)

  obtain ⟨c, hinf, hfin⟩ := crt_covering b
  refine ⟨c, ?_, ?_⟩
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w (c - a (.infinite w) hv) ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_pos hv] at hinf_w
      rw [placeNorm_infinite_eq_norm_algebraMap, RingHom.map_sub, norm_sub_rev]
      exact hinf_w
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi (c - a (.finite vi) hv) ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_pos hv] at hfin_vi
      rw [show c - a (.finite vi) hv = -(a (.finite vi) hv - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (a (.finite vi) hv - c)
        (by rw [RingHom.map_sub]; exact hfin_vi)) (one_le_coveringBound K)
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w c ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_neg hv] at hinf_w
      rw [placeNorm_infinite_eq_norm_algebraMap]
      calc ‖algebraMap K w.Completion c‖
          = ‖0 - algebraMap K w.Completion c‖ := by rw [zero_sub, norm_neg]
        _ ≤ coveringBound K := hinf_w
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi c ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_neg hv] at hfin_vi
      rw [show c = -(0 - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (0 - c)
        (by rw [RingHom.map_sub, RingHom.map_zero]; exact hfin_vi)) (one_le_coveringBound K)

theorem adelic_scaling_decomposition
    (u : K) (hu : u ≠ 0)
    (S : Finset (Place K)) (a : (v : Place K) → v ∈ S → K) :
    ∃ (x : K),
      (∀ v (hv : v ∈ S), placeNorm v (x - a v hv) ≤ placeNorm v u * coveringBound K) ∧
      (∀ v : Place K, v ∉ S → placeNorm v x ≤ placeNorm v u * coveringBound K) := by

  obtain ⟨c, hc_S, hc_T⟩ := adeles_K_plus_unit_ball S (fun v hv => u⁻¹ * a v hv)

  refine ⟨u * c, fun v hv => ?_, fun v hv => ?_⟩
  ·
    have key : u * c - a v hv = u * (c - u⁻¹ * a v hv) := by field_simp
    rw [key, placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_S v hv) (placeNorm_nonneg v u)
  ·
    rw [placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_T v hv) (placeNorm_nonneg v u)

theorem strong_approximation
    (S : Finset (Place K)) (w : Place K) (hw : w ∉ S)
    (a : (v : Place K) → v ∈ S → K) (ε : (v : Place K) → v ∈ S → ℝ)
    (hε : ∀ v (hv : v ∈ S), 0 < ε v hv) :
    ∃ (x : K),
      (∀ v (hv : v ∈ S), placeNorm v (x - a v hv) ≤ ε v hv) ∧
      (∀ v : Place K, v ∉ S → v ≠ w → placeNorm v x ≤ 1) := by


  let CB := coveringBound K
  have hCB_pos : (0 : ℝ) < CB := coveringBound_pos K
  have hCB_ne : CB ≠ 0 := coveringBound_ne_zero K

  let extraInf : Finset (Place K) :=
    (Finset.univ.image Place.infinite).filter (fun v => v ∉ S ∧ v ≠ w)
  let S' : Finset (Place K) := S ∪ extraInf
  have hS_sub_S' : S ⊆ S' := Finset.subset_union_left
  have hw' : w ∉ S' := by
    simp only [S', Finset.mem_union]
    push Not
    constructor
    · exact hw
    · intro hmem
      simp only [extraInf, Finset.mem_filter] at hmem
      exact hmem.2.2 rfl

  let ε' : (v : Place K) → v ∈ S' → ℝ := fun v hv =>
    if h : v ∈ S then ε v h / CB else 1 / CB
  have hε' : ∀ v (hv : v ∈ S'), 0 < ε' v hv := by
    intro v hv
    simp only [ε']
    split_ifs with h
    · exact div_pos (hε v h) hCB_pos
    · exact div_pos one_pos hCB_pos

  obtain ⟨u, hu_ne, hu_S', hu_T'⟩ :=
    exists_element_with_controlled_norms S' w hw' ε' hε'


  let scaledTargets : (v : Place K) → v ∈ S → K := fun v hv => u⁻¹ * a v hv
  let finPartFun : ∀ vi : HeightOneSpectrum (𝓞 K), vi.adicCompletion K := fun vi =>
    if h : Place.finite vi ∈ S
    then algebraMap K (vi.adicCompletion K) (scaledTargets (.finite vi) h)
    else 0
  have hfin_mem : ∀ᶠ vi in Filter.cofinite,
      finPartFun vi ∈ (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) := by
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.Finite.preimage
      (fun v₁ _ v₂ _ h => Place.finite.inj h) S.finite_toSet)
    intro vi hvi
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe] at *
    by_contra hmem
    exact hvi (by simp only [finPartFun, dif_neg hmem]; exact (vi.adicCompletionIntegers K).zero_mem)
  let b : adeleRing (K := K) :=
    ((fun w => if h : Place.infinite w ∈ S
      then algebraMap K w.Completion (scaledTargets (.infinite w) h) else 0),
     ⟨finPartFun, hfin_mem⟩)
  obtain ⟨c, hinf, hfin⟩ := crt_covering b

  let x := u * c


  refine ⟨x, fun v hv => ?_, fun v hv_notS hv_neW => ?_⟩
  ·
    have key : x - a v hv = u * (c - scaledTargets v hv) := by
      show u * c - a v hv = u * (c - u⁻¹ * a v hv)
      field_simp
    rw [key, placeNorm_mul]
    have hu_v : placeNorm v u ≤ ε v hv / CB := by
      have hv' : v ∈ S' := hS_sub_S' hv
      have := hu_S' v hv'
      simp only [ε', dif_pos hv] at this
      exact this

    have hc_bound : placeNorm v (c - scaledTargets v hv) ≤ CB := by
      match v with
      | .infinite w =>
        show w (c - scaledTargets (.infinite w) hv) ≤ CB
        have hinf_w := hinf w
        change ‖(if h : Place.infinite w ∈ S
          then algebraMap K w.Completion (scaledTargets (.infinite w) h) else 0) -
          algebraMap K w.Completion c‖ ≤ CB at hinf_w
        simp only [dif_pos hv] at hinf_w
        rw [placeNorm_infinite_eq_norm_algebraMap, RingHom.map_sub, norm_sub_rev]
        exact hinf_w
      | .finite vi =>
        show NumberField.HeightOneSpectrum.adicAbv K vi (c - scaledTargets (.finite vi) hv) ≤ CB
        have hfin_vi := hfin vi
        change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
          (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
        simp only [finPartFun, dif_pos hv] at hfin_vi
        rw [show c - scaledTargets (.finite vi) hv = -(scaledTargets (.finite vi) hv - c) from by ring]
        rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
        exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi
          (scaledTargets (.finite vi) hv - c)
          (by rw [RingHom.map_sub]; exact hfin_vi)) (one_le_coveringBound K)
    calc placeNorm v u * placeNorm v (c - scaledTargets v hv)
        ≤ placeNorm v u * CB :=
          mul_le_mul_of_nonneg_left hc_bound (placeNorm_nonneg v u)
      _ ≤ (ε v hv / CB) * CB :=
          mul_le_mul_of_nonneg_right hu_v (le_of_lt hCB_pos)
      _ = ε v hv := by field_simp
  ·
    show placeNorm v (u * c) ≤ 1
    rw [placeNorm_mul]
    match v with
    | .finite vi =>

      have hu_le : placeNorm (.finite vi) u ≤ 1 := by
        by_cases hmem : Place.finite vi ∈ S'
        · exfalso
          simp only [S', Finset.mem_union] at hmem
          rcases hmem with hS | hExtr
          · exact hv_notS hS
          · simp only [extraInf, Finset.mem_filter, Finset.mem_image,
              Finset.mem_univ, true_and] at hExtr
            obtain ⟨⟨_, hinj⟩, _⟩ := hExtr
            cases hinj
        · exact hu_T' (.finite vi) hmem hv_neW

      have hc_le : placeNorm (.finite vi) c ≤ 1 := by
        show NumberField.HeightOneSpectrum.adicAbv K vi c ≤ 1
        have hfin_vi := hfin vi
        change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
          (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
        simp only [finPartFun, dif_neg hv_notS] at hfin_vi
        rw [show c = -(0 - c) from by ring]
        rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
        exact adicAbv_le_one_of_mem_integers_algebraMap vi (0 - c)
          (by rw [RingHom.map_sub, RingHom.map_zero]; exact hfin_vi)
      calc placeNorm (.finite vi) u * placeNorm (.finite vi) c
          ≤ 1 * 1 := mul_le_mul hu_le hc_le (placeNorm_nonneg _ _) zero_le_one
        _ = 1 := one_mul 1
    | .infinite winf =>

      have hv_in_S' : Place.infinite winf ∈ S' := by
        simp only [S', Finset.mem_union]
        by_cases hS : Place.infinite winf ∈ S
        · exact Or.inl hS
        · right
          simp only [extraInf, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨⟨winf, rfl⟩, hS, hv_neW⟩
      have hu_v : placeNorm (.infinite winf) u ≤ 1 / CB := by
        have := hu_S' (.infinite winf) hv_in_S'
        simp only [ε', dif_neg hv_notS] at this
        exact this

      have hc_bound : placeNorm (.infinite winf) c ≤ CB := by
        show winf c ≤ CB
        have hinf_w := hinf winf
        change ‖(if h : Place.infinite winf ∈ S
          then algebraMap K winf.Completion (scaledTargets (.infinite winf) h) else 0) -
          algebraMap K winf.Completion c‖ ≤ CB at hinf_w
        simp only [dif_neg hv_notS] at hinf_w
        rw [placeNorm_infinite_eq_norm_algebraMap]
        calc ‖algebraMap K winf.Completion c‖
            = ‖0 - algebraMap K winf.Completion c‖ := by rw [zero_sub, norm_neg]
          _ ≤ CB := hinf_w
      calc placeNorm (.infinite winf) u * placeNorm (.infinite winf) c
          ≤ (1 / CB) * CB := by
            exact mul_le_mul hu_v hc_bound (placeNorm_nonneg _ _) (by positivity)
        _ = 1 := by field_simp

theorem global_field_dense_awayFrom
    (w : Place K) (S : Finset (Place K)) (hw : w ∉ S)
    (a : (v : Place K) → v ∈ S → K) (ε : ℝ) (hε : 0 < ε) :
    ∃ (x : K),
      (∀ v (hv : v ∈ S), placeNorm v (x - a v hv) ≤ ε) ∧
      (∀ v : Place K, v ∉ S → v ≠ w → placeNorm v x ≤ 1) :=
  strong_approximation S w hw a (fun _ _ => ε) (fun _ _ => hε)

lemma placeNorm_finite_le_one_imp_mem_integers (v : HeightOneSpectrum (𝓞 K)) (x : K)
    (hx : placeNorm (.finite v) x ≤ 1) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [SetLike.mem_coe, mem_adicCompletionIntegers_iff_norm_le_one]
  show ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v‖ ≤ 1
  have : (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v = algebraMap K (v.adicCompletion K) x := rfl
  rw [this]
  have : algebraMap K (v.adicCompletion K) x = FinitePlace.embedding v x := rfl
  rw [this, FinitePlace.norm_embedding]
  exact hx

lemma algebraMap_finiteAdeleRing_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v = algebraMap K (v.adicCompletion K) x := rfl

lemma norm_algebraMap_finiteAdeleRing_eq (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v‖ = placeNorm (.finite v) x := by
  show ‖algebraMap K (v.adicCompletion K) x‖ = HeightOneSpectrum.adicAbv K v x
  rw [show algebraMap K (v.adicCompletion K) x = FinitePlace.embedding v x from rfl]
  rw [FinitePlace.norm_embedding]

lemma strong_approx_integral_to_mem_integers (x : K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hx : ∀ (v : HeightOneSpectrum (𝓞 K)), v ∉ S →
      placeNorm (.finite v) x ≤ 1) :
    ∀ (v : HeightOneSpectrum (𝓞 K)), v ∉ S →
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  fun v hv => placeNorm_finite_le_one_imp_mem_integers v x (hx v hv)

lemma norm_algebraMap_finiteAdeleRing_sub (v : HeightOneSpectrum (𝓞 K)) (x y : K) :
    ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v -
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) y) v‖ =
    placeNorm (.finite v) (x - y) := by
  have : (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v -
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) y) v =
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) (x - y)) v := by
    show algebraMap K (v.adicCompletion K) x - algebraMap K (v.adicCompletion K) y =
      algebraMap K (v.adicCompletion K) (x - y)
    rw [map_sub]
  rw [this, norm_algebraMap_finiteAdeleRing_eq]

lemma algebraMap_finiteAdeleRing_sub_apply (v : HeightOneSpectrum (𝓞 K)) (x y : K) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) (x - y)) v =
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v -
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) y) v := by
  show algebraMap K (v.adicCompletion K) (x - y) =
    algebraMap K (v.adicCompletion K) x - algebraMap K (v.adicCompletion K) y
  rw [map_sub]

theorem adeles_K_plus_unit_ball_finite_le_one
    (S : Finset (Place K)) (a : (v : Place K) → v ∈ S → K) :
    ∃ (c : K),
      (∀ v (hv : v ∈ S), placeNorm v (c - a v hv) ≤ coveringBound K) ∧
      (∀ v : Place K, v ∉ S → placeNorm v c ≤ coveringBound K) ∧
      (∀ (vi : HeightOneSpectrum (𝓞 K)), Place.finite vi ∉ S →
        placeNorm (.finite vi) c ≤ 1) := by

  let finPartFun : ∀ vi : HeightOneSpectrum (𝓞 K), vi.adicCompletion K := fun vi =>
    if h : Place.finite vi ∈ S
    then algebraMap K (vi.adicCompletion K) (a (.finite vi) h)
    else 0
  have hfin_mem : ∀ᶠ vi in Filter.cofinite,
      finPartFun vi ∈ (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) := by
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.Finite.preimage
      (fun v₁ _ v₂ _ h => Place.finite.inj h) S.finite_toSet)
    intro vi hvi
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe] at *
    by_contra hmem
    exact hvi (by simp only [finPartFun, dif_neg hmem]; exact (vi.adicCompletionIntegers K).zero_mem)
  let b : adeleRing (K := K) :=
    ((fun w => if h : Place.infinite w ∈ S
      then algebraMap K w.Completion (a (.infinite w) h) else 0),
     ⟨finPartFun, hfin_mem⟩)

  obtain ⟨c, hinf, hfin⟩ := crt_covering b
  refine ⟨c, ?_, ?_, ?_⟩
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w (c - a (.infinite w) hv) ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_pos hv] at hinf_w
      rw [placeNorm_infinite_eq_norm_algebraMap, RingHom.map_sub, norm_sub_rev]
      exact hinf_w
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi (c - a (.finite vi) hv) ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_pos hv] at hfin_vi
      rw [show c - a (.finite vi) hv = -(a (.finite vi) hv - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (a (.finite vi) hv - c)
        (by rw [RingHom.map_sub]; exact hfin_vi)) (one_le_coveringBound K)
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w c ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_neg hv] at hinf_w
      rw [placeNorm_infinite_eq_norm_algebraMap]
      calc ‖algebraMap K w.Completion c‖
          = ‖0 - algebraMap K w.Completion c‖ := by rw [zero_sub, norm_neg]
        _ ≤ coveringBound K := hinf_w
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi c ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_neg hv] at hfin_vi
      rw [show c = -(0 - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (0 - c)
        (by rw [RingHom.map_sub, RingHom.map_zero]; exact hfin_vi)) (one_le_coveringBound K)
  ·
    intro vi hvi
    have hfin_vi := hfin vi
    show NumberField.HeightOneSpectrum.adicAbv K vi c ≤ 1
    change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
      (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
    simp only [finPartFun, dif_neg hvi] at hfin_vi
    rw [show c = -(0 - c) from by ring]
    rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
    exact adicAbv_le_one_of_mem_integers_algebraMap vi (0 - c)
      (by rw [RingHom.map_sub, RingHom.map_zero]; exact hfin_vi)

theorem adelic_scaling_decomposition_finite_le_one
    (u : K) (hu : u ≠ 0)
    (S : Finset (Place K)) (a : (v : Place K) → v ∈ S → K) :
    ∃ (x : K),
      (∀ v (hv : v ∈ S), placeNorm v (x - a v hv) ≤ placeNorm v u * coveringBound K) ∧
      (∀ v : Place K, v ∉ S → placeNorm v x ≤ placeNorm v u * coveringBound K) ∧
      (∀ (vi : HeightOneSpectrum (𝓞 K)), Place.finite vi ∉ S →
        placeNorm (.finite vi) x ≤ placeNorm (.finite vi) u * 1) := by
  obtain ⟨c, hc_S, hc_T, hc_fin⟩ := adeles_K_plus_unit_ball_finite_le_one S (fun v hv => u⁻¹ * a v hv)
  refine ⟨u * c, fun v hv => ?_, fun v hv => ?_, fun vi hvi => ?_⟩
  · have key : u * c - a v hv = u * (c - u⁻¹ * a v hv) := by field_simp
    rw [key, placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_S v hv) (placeNorm_nonneg v u)
  · rw [placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_T v hv) (placeNorm_nonneg v u)
  · rw [placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_fin vi hvi) (placeNorm_nonneg (.finite vi) u)

theorem strong_approximation_finite_le_one
    (S : Finset (Place K)) (w : Place K) (hw : w ∉ S)
    (a : (v : Place K) → v ∈ S → K) (ε : (v : Place K) → v ∈ S → ℝ)
    (hε : ∀ v (hv : v ∈ S), 0 < ε v hv) :
    ∃ (x : K),
      (∀ v (hv : v ∈ S), placeNorm v (x - a v hv) ≤ ε v hv) ∧
      (∀ v : Place K, v ∉ S → v ≠ w → placeNorm v x ≤ 1) ∧
      (∀ (vi : HeightOneSpectrum (𝓞 K)), Place.finite vi ∉ S →
        Place.finite vi ≠ w → placeNorm (.finite vi) x ≤ 1) := by
  obtain ⟨x, hx_close, hx_T⟩ := strong_approximation S w hw a ε hε
  exact ⟨x, hx_close, hx_T, fun vi hvi hvi_ne_w => hx_T (.finite vi) hvi hvi_ne_w⟩

set_option maxHeartbeats 800000 in
theorem denseRange_algebraMap_finiteAdeleRing :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU_nhds
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _

  set S_y : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}
  have hS_y : Filter.cofinite ≤ Filter.principal S_y := Filter.le_principal_iff.mpr y.2

  have hy_lift := RestrictedProduct.exists_inclusion_eq_of_eventually
    (fun v => v.adicCompletion K)
    (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    hS_y (show ∀ᶠ v in Filter.principal S_y,
      y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) from
      Filter.eventually_principal.mpr (fun v hv => hv))
  obtain ⟨y', hy'_eq⟩ := hy_lift

  have hU_mem : U ∈ Filter.map (RestrictedProduct.inclusion _ _ hS_y) (nhds y') := by
    rwa [← RestrictedProduct.nhds_eq_map_inclusion hAopen hS_y y', hy'_eq]
  have hU_preimage := Filter.mem_map.mp hU_mem
  rw [RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap y'] at hU_preimage
  rw [Filter.mem_comap] at hU_preimage

  obtain ⟨V, hV_nhds, hV_sub⟩ := hU_preimage

  rw [nhds_pi, Filter.mem_pi] at hV_nhds
  obtain ⟨T, hT_fin, W, hW_mem, hW_sub⟩ := hV_nhds

  set T_fin := hT_fin.toFinset with hT_fin_def


  have hW_nhds_y : ∀ v ∈ T, W v ∈ nhds (y v) := by
    intro v hv
    have heq : (↑y' : ∀ w, w.adicCompletion K) v = y v := by
      have : (Subtype.val (RestrictedProduct.inclusion _ _ hS_y y')) v = (Subtype.val y) v := by
        rw [hy'_eq]
      exact this
    rw [← heq]; exact hW_mem v


  have h_W_ball : ∀ v ∈ T, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (y v) ε ⊆ W v := by
    intro v hv
    exact Metric.nhds_basis_ball.mem_iff.mp (hW_nhds_y v hv)
  choose ε_W hε_W_pos hε_W_sub using h_W_ball

  have hK_dense : ∀ v : HeightOneSpectrum (𝓞 K),
      DenseRange (algebraMap K (v.adicCompletion K)) :=
    fun v => v.denseRange_algebraMap K

  have h_approx : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T), ∃ a : K,
      ‖algebraMap K (v.adicCompletion K) a - y v‖ < min (ε_W v hv) 1 / 4 := by
    intro v hv
    have hpos : (0 : ℝ) < min (ε_W v hv) 1 / 4 := by
      have := hε_W_pos v hv; positivity
    obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp (hK_dense v) (y v) _ hpos
    exact ⟨a, by rwa [dist_comm, dist_eq_norm] at ha⟩

  choose a_fun ha_fun using h_approx

  have ⟨w_inf⟩ : Nonempty (InfinitePlace K) := inferInstance
  set S_place : Finset (Place K) := T_fin.image Place.finite
  have hw : Place.infinite w_inf ∉ S_place := by
    simp only [S_place, Finset.mem_image]; rintro ⟨_, _, h⟩; exact (by exact nofun : Place.finite _ ≠ Place.infinite _) h

  have hT_mem : ∀ v ∈ T, v ∈ T_fin := by
    intro v hv; rw [hT_fin_def]; exact hT_fin.mem_toFinset.mpr hv

  have hfin_in_T : ∀ (vi : HeightOneSpectrum (𝓞 K)),
      Place.finite vi ∈ S_place → vi ∈ T := by
    intro vi hv
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
    exact hT_fin.mem_toFinset.mp (Place.finite.inj he ▸ hw)


  let sa_target : (v : Place K) → v ∈ S_place → K := fun v _ =>
    match v with
    | .finite vi => a_fun vi (hfin_in_T vi ‹_›)
    | .infinite _ => 0
  let sa_eps : (v : Place K) → v ∈ S_place → ℝ := fun v _ =>
    match v with
    | .finite vi => min (ε_W vi (hfin_in_T vi ‹_›)) 1 / 4
    | .infinite _ => 1
  have sa_eps_pos : ∀ v (hv : v ∈ S_place), 0 < sa_eps v hv := by
    intro v hv
    match v with
    | .finite vi => exact div_pos (lt_min (hε_W_pos vi (hfin_in_T vi hv)) one_pos) (by norm_num)
    | .infinite _ => exact one_pos
  obtain ⟨x, hx_close, _, hx_int⟩ := strong_approximation_finite_le_one
    S_place (Place.infinite w_inf) hw sa_target sa_eps sa_eps_pos
  set fx := algebraMap K (FiniteAdeleRing (𝓞 K) K) x with hfx_def

  refine ⟨fx, ?_, x, rfl⟩


  have hfx_int : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
      fx v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v hv
    apply placeNorm_finite_le_one_imp_mem_integers
    apply hx_int v
    · simp only [S_place, Finset.mem_image]
      intro ⟨w, hw, he⟩
      exact hv (hT_fin.mem_toFinset.mp (Place.finite.inj he ▸ hw))
    · exact nofun

  have hfx_close : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      ‖fx v - y v‖ ≤ min (ε_W v hv) 1 / 2 := by
    intro v hv
    have hmem_S : Place.finite v ∈ S_place :=
      Finset.mem_image.mpr ⟨v, hT_mem v hv, rfl⟩
    have h1 : placeNorm (.finite v) (x - a_fun v hv) ≤ min (ε_W v hv) 1 / 4 :=
      hx_close (.finite v) hmem_S
    have h2 := ha_fun v hv

    have hnorm_eq : ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) (x - a_fun v hv)) v‖ =
        placeNorm (.finite v) (x - a_fun v hv) :=
      norm_algebraMap_finiteAdeleRing_eq v (x - a_fun v hv)
    calc ‖fx v - y v‖
        = ‖(fx v - algebraMap K (v.adicCompletion K) (a_fun v hv)) +
            (algebraMap K (v.adicCompletion K) (a_fun v hv) - y v)‖ := by
          congr 1; abel
      _ ≤ ‖fx v - algebraMap K (v.adicCompletion K) (a_fun v hv)‖ +
            ‖algebraMap K (v.adicCompletion K) (a_fun v hv) - y v‖ := norm_add_le _ _
      _ = ‖algebraMap K (v.adicCompletion K) (x - a_fun v hv)‖ +
            ‖algebraMap K (v.adicCompletion K) (a_fun v hv) - y v‖ := by
          congr 1
          show ‖algebraMap K (v.adicCompletion K) x -
            algebraMap K (v.adicCompletion K) (a_fun v hv)‖ = _
          rw [← map_sub]
      _ ≤ min (ε_W v hv) 1 / 4 + min (ε_W v hv) 1 / 4 := by
          have : ‖algebraMap K (v.adicCompletion K) (x - a_fun v hv)‖ =
              placeNorm (.finite v) (x - a_fun v hv) := hnorm_eq
          linarith
      _ = min (ε_W v hv) 1 / 2 := by ring

  have hfx_in_W : ∀ v ∈ T, fx v ∈ W v := by
    intro v hv
    apply hε_W_sub v hv
    rw [Metric.mem_ball, dist_eq_norm]
    have hclose := hfx_close v hv
    calc ‖fx v - y v‖ ≤ min (ε_W v hv) 1 / 2 := hclose
      _ ≤ ε_W v hv / 2 := by
          apply div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0:ℝ) ≤ 2)
      _ < ε_W v hv := by linarith [hε_W_pos v hv]

  have hfx_int_T : ∀ v ∈ T, v ∈ S_y →
      fx v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v hv hv_S
    rw [SetLike.mem_coe, mem_adicCompletionIntegers_iff_norm_le_one]
    have hclose : ‖fx v - y v‖ ≤ 1 := by
      have hlt := hfx_close v hv
      have hle : min (ε_W v hv) 1 / 2 ≤ 1 := by
        calc min (ε_W v hv) 1 / 2 ≤ 1 / 2 := by
              apply div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0:ℝ) ≤ 2)
            _ ≤ 1 := by norm_num
      linarith
    have hy_norm : ‖y v‖ ≤ 1 := by
      rw [← mem_adicCompletionIntegers_iff_norm_le_one]; exact hv_S
    rw [show (fx v : v.adicCompletion K) = (fx v - y v) + y v from by abel]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hclose hy_norm)

  have hfx_S_y : ∀ v ∈ S_y, fx v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v hv
    by_cases hv_T : v ∈ T
    · exact hfx_int_T v hv_T hv
    · exact hfx_int v hv_T

  have hfx_ev : ∀ᶠ v in Filter.principal S_y,
      fx v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Filter.eventually_principal.mpr hfx_S_y
  have hfx_lift := RestrictedProduct.exists_inclusion_eq_of_eventually
    (fun v => v.adicCompletion K)
    (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    hS_y hfx_ev
  obtain ⟨fx', hfx'_eq⟩ := hfx_lift

  rw [show fx = RestrictedProduct.inclusion _ _ hS_y fx' from hfx'_eq.symm]
  apply hV_sub
  apply hW_sub
  intro v hv


  show (↑fx' : ∀ w, w.adicCompletion K) v ∈ W v
  have : (RestrictedProduct.inclusion _ _ hS_y fx') v = (↑fx' : ∀ w, w.adicCompletion K) v := rfl
  rw [← this, hfx'_eq]
  exact hfx_in_W v hv

theorem global_field_dense_in_infiniteAdeleRing :
    Dense (Set.range (algebraMap K (InfiniteAdeleRing K))) :=
  InfiniteAdeleRing.denseRange_algebraMap K

theorem denseRange_algebraMap_adeleRing_components :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) ∧
    DenseRange (algebraMap K (InfiniteAdeleRing K)) :=
  ⟨denseRange_algebraMap_finiteAdeleRing, global_field_dense_in_infiniteAdeleRing⟩

@[reducible]
def placeCompletion : Place K → Type _
  | .finite vi => vi.adicCompletion K
  | .infinite w => w.Completion

instance instTopologicalSpacePlaceCompletion (v : Place K) :
    TopologicalSpace (placeCompletion v) := by
  cases v with
  | finite vi => exact inferInstance
  | infinite w => exact inferInstance

def placeIntegerSet : (v : Place K) → Set (placeCompletion v)
  | .finite vi => (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))
  | .infinite _ => Set.univ

abbrev restrictedProductAwayFrom (w : Place K) : Type _ :=
  RestrictedProduct
    (fun (v : {v : Place K // v ≠ w}) => placeCompletion v.val)
    (fun (v : {v : Place K // v ≠ w}) => placeIntegerSet v.val)
    Filter.cofinite

@[reducible]
def embedAtPlace : (v : Place K) → K → placeCompletion v
  | .finite vi => algebraMap K (vi.adicCompletion K)
  | .infinite w => algebraMap K w.Completion

def diagonalAwayFrom (w : Place K) (x : K) : restrictedProductAwayFrom w :=
  RestrictedProduct.mk
    (fun (v : {v : Place K // v ≠ w}) => embedAtPlace v.val x)
    (by


     rw [Filter.eventually_cofinite]

     set f : {v : Place K // v ≠ w} → Option (HeightOneSpectrum (𝓞 K)) :=
       fun i => match i.val with
         | .finite vi => some vi
         | .infinite _ => none
     apply Set.Finite.of_injOn (f := f)
       (t := Option.some '' HeightOneSpectrum.Support (𝓞 K) x)
     ·
       intro ⟨v, hv⟩ hmem
       simp only [Set.mem_setOf_eq] at hmem
       cases v with
       | infinite _ => simp [placeIntegerSet] at hmem
       | finite vi =>
         simp only [f, Set.mem_image]
         refine ⟨vi, ?_, rfl⟩
         rw [HeightOneSpectrum.Support, Set.mem_setOf_eq]
         simp only [placeIntegerSet, SetLike.mem_coe, embedAtPlace] at hmem
         rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hmem
         have : algebraMap K (vi.adicCompletion K) x = (x : vi.adicCompletion K) := rfl
         rw [this] at hmem
         rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hmem
     ·
       intro ⟨v₁, hv₁⟩ hmem₁ ⟨v₂, hv₂⟩ hmem₂ hfeq
       simp only [Set.mem_setOf_eq] at hmem₁ hmem₂
       cases v₁ with
       | infinite _ => simp [placeIntegerSet] at hmem₁
       | finite vi₁ =>
         cases v₂ with
         | infinite _ => simp [placeIntegerSet] at hmem₂
         | finite vi₂ =>
           simp only [f] at hfeq
           have : vi₁ = vi₂ := Option.some_injective _ hfeq
           subst this; rfl
     ·
       exact (HeightOneSpectrum.Support.finite (𝓞 K) x).image _)

lemma isOpen_placeIntegerSet (v : Place K) : IsOpen (placeIntegerSet v) := by
  cases v with
  | finite vi => exact Valued.isOpen_valuationSubring _
  | infinite _ => exact isOpen_univ

lemma placeNorm_le_one_imp_mem_placeIntegerSet (v : Place K) (x : K)
    (hx : placeNorm v x ≤ 1) : embedAtPlace v x ∈ placeIntegerSet v := by
  cases v with
  | finite vi =>
    show algebraMap K (vi.adicCompletion K) x ∈
      (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))
    rw [SetLike.mem_coe, mem_adicCompletionIntegers_iff_norm_le_one]
    rw [show algebraMap K (vi.adicCompletion K) x = FinitePlace.embedding vi x from rfl,
        FinitePlace.norm_embedding]
    exact hx
  | infinite _ => exact Set.mem_univ _

omit [NumberField K] in
lemma infPlace_norm_algebraMap (wi : InfinitePlace K) (x : K) :
    ‖algebraMap K wi.Completion x‖ = wi.1 x := by
  change ‖(↑((WithAbs.equiv wi.1).symm x) :
    UniformSpace.Completion (WithAbs wi.1))‖ = _
  rw [UniformSpace.Completion.norm_coe]; rfl

omit [NumberField K] in
lemma infPlace_denseRange_algebraMap (wi : InfinitePlace K) :
    DenseRange (algebraMap K wi.Completion) := by
  suffices h : DenseRange (UniformSpace.Completion.coe' ∘
      (WithAbs.equiv wi.1).symm : K → UniformSpace.Completion (WithAbs wi.1)) from h
  exact DenseRange.comp
    (@UniformSpace.Completion.denseRange_coe (WithAbs wi.1) _)
    ((WithAbs.equiv wi.1).symm.surjective.denseRange)
    (UniformSpace.Completion.continuous_coe _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 40000 in
theorem dense_diagonalAwayFrom (w : Place K) :
    Dense (Set.range (diagonalAwayFrom w)) := by

  intro y
  rw [mem_closure_iff_nhds]
  intro U hU_nhds
  have hAopen : ∀ v : {v : Place K // v ≠ w}, IsOpen (placeIntegerSet v.val) :=
    fun v => isOpen_placeIntegerSet v.val
  let S_y : Set {v : Place K // v ≠ w} := {v | y.val v ∈ placeIntegerSet v.val}
  have hS_y : Filter.cofinite ≤ Filter.principal S_y := Filter.le_principal_iff.mpr y.2
  obtain ⟨y', hy'_eq⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually
    (fun (v : {v : Place K // v ≠ w}) => placeCompletion v.val)
    (fun (v : {v : Place K // v ≠ w}) => placeIntegerSet v.val)
    hS_y (Filter.eventually_principal.mpr (fun _ hv => hv))
  have hU_mem : U ∈ Filter.map (RestrictedProduct.inclusion _ _ hS_y) (nhds y') := by
    rwa [← RestrictedProduct.nhds_eq_map_inclusion hAopen hS_y y', hy'_eq]
  rw [Filter.mem_map,
      RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap y',
      Filter.mem_comap] at hU_mem
  obtain ⟨V, hV_nhds, hV_sub⟩ := hU_mem
  rw [nhds_pi, Filter.mem_pi] at hV_nhds
  obtain ⟨T, hT_fin, W, hW_mem, hW_sub⟩ := hV_nhds
  set T_fin := hT_fin.toFinset with hT_fin_def
  have hW_nhds_y : ∀ v ∈ T, W v ∈ nhds (y.val v) := by
    intro v hv
    have heq : (↑y' : ∀ i, placeCompletion i.val) v = y.val v :=
      congr_fun (congrArg Subtype.val hy'_eq) v
    rw [← heq]; exact hW_mem v
  set S_place : Finset (Place K) := T_fin.image Subtype.val with hS_place_def
  have hw_not_in : w ∉ S_place := by
    simp only [S_place, Finset.mem_image]; rintro ⟨v, _, hv_eq⟩; exact v.2 hv_eq
  have hT_mem : ∀ v ∈ T, v ∈ T_fin := fun v hv => hT_fin.mem_toFinset.mpr hv
  have hval_in_T : ∀ (v : {v : Place K // v ≠ w}), v.val ∈ S_place → v ∈ T := by
    intro v hv
    obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp hv
    exact hT_fin.mem_toFinset.mp (Subtype.val_injective hu_eq ▸ hu)

  have h_targets : ∀ (v : {v : Place K // v ≠ w}), v ∈ T →
      ∃ (a : K) (ε : ℝ), 0 < ε ∧ ε ≤ 1 ∧
        (∀ z : K, placeNorm v.val (z - a) ≤ ε → embedAtPlace v.val z ∈ W v) ∧
        (y.val v ∈ placeIntegerSet v.val →
          ∀ z : K, placeNorm v.val (z - a) ≤ ε →
            embedAtPlace v.val z ∈ placeIntegerSet v.val) := by
    intro ⟨p, hp⟩ hpT
    cases p with
    | finite vi =>
      have hW' := hW_nhds_y ⟨.finite vi, hp⟩ hpT
      obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.nhds_basis_ball.mem_iff.mp hW'
      obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp (vi.denseRange_algebraMap K)
        (y.val ⟨.finite vi, hp⟩) (min ε 1 / 4) (by positivity)
      refine ⟨a, min ε 1 / 4, by positivity,
        le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)) (by norm_num),
        fun z hz => ?_, fun hy_int z hz => ?_⟩
      · apply hε_sub; rw [Metric.mem_ball]
        have h2 : dist (algebraMap K (vi.adicCompletion K) a)
            (algebraMap K (vi.adicCompletion K) z) ≤ min ε 1 / 4 := by
          rw [dist_eq_norm, ← map_sub]
          show ‖FinitePlace.embedding vi (a - z)‖ ≤ _
          rw [FinitePlace.norm_embedding]
          rwa [show (HeightOneSpectrum.adicAbv K vi) (a - z) =
            (HeightOneSpectrum.adicAbv K vi) (z - a) from
            AbsoluteValue.map_sub _ a z]
        calc dist (algebraMap K (vi.adicCompletion K) z) (y.val ⟨.finite vi, hp⟩)
            ≤ dist (algebraMap K (vi.adicCompletion K) z)
                (algebraMap K (vi.adicCompletion K) a) +
              dist (algebraMap K (vi.adicCompletion K) a)
                (y.val ⟨.finite vi, hp⟩) := dist_triangle _ _ _
          _ ≤ min ε 1 / 4 + min ε 1 / 4 := by
              have hd1 : dist (algebraMap K (vi.adicCompletion K) z)
                  (algebraMap K (vi.adicCompletion K) a) ≤ min ε 1 / 4 := by
                rw [dist_comm]; exact h2
              have hd2 : dist (algebraMap K (vi.adicCompletion K) a)
                  (y.val ⟨.finite vi, hp⟩) ≤ min ε 1 / 4 := by
                rw [dist_comm]; linarith
              linarith
          _ ≤ ε / 4 + ε / 4 := by
              gcongr <;> exact min_le_left _ _

          _ < ε := by linarith

      · show algebraMap K (vi.adicCompletion K) z ∈
          (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))
        rw [SetLike.mem_coe, mem_adicCompletionIntegers_iff_norm_le_one]
        have hy_norm : ‖y.val ⟨.finite vi, hp⟩‖ ≤ 1 := by
          have := hy_int; simp only [placeIntegerSet, SetLike.mem_coe] at this
          rwa [mem_adicCompletionIntegers_iff_norm_le_one] at this
        have hz_a_norm : ‖algebraMap K (vi.adicCompletion K) z -
            algebraMap K (vi.adicCompletion K) a‖ ≤ 1 := by
          rw [← map_sub]; show ‖FinitePlace.embedding vi (z - a)‖ ≤ 1
          rw [FinitePlace.norm_embedding]
          have hle1 : min ε 1 / 4 ≤ 1 :=
            le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)) (by norm_num)
          have hz' : (HeightOneSpectrum.adicAbv K vi) (z - a) ≤ min ε 1 / 4 := hz
          linarith

        have ha_y_norm : ‖algebraMap K (vi.adicCompletion K) a -
            y.val ⟨.finite vi, hp⟩‖ ≤ 1 := by
          rw [← dist_eq_norm]
          have : dist (algebraMap K (vi.adicCompletion K) a)
              (y.val ⟨.finite vi, hp⟩) < min ε 1 / 4 := by rw [dist_comm]; exact ha
          linarith [div_le_div_of_nonneg_right (min_le_right ε 1) (by positivity : (0:ℝ) ≤ 4)]
        rw [show algebraMap K (vi.adicCompletion K) z =
            (algebraMap K (vi.adicCompletion K) z - algebraMap K (vi.adicCompletion K) a) +
            (algebraMap K (vi.adicCompletion K) a - y.val ⟨.finite vi, hp⟩) +
            y.val ⟨.finite vi, hp⟩ from by ring]
        calc ‖(algebraMap K (vi.adicCompletion K) z - algebraMap K (vi.adicCompletion K) a) +
              (algebraMap K (vi.adicCompletion K) a - y.val ⟨.finite vi, hp⟩) +
              y.val ⟨.finite vi, hp⟩‖
            ≤ max (‖(algebraMap K (vi.adicCompletion K) z - algebraMap K (vi.adicCompletion K) a) +
              (algebraMap K (vi.adicCompletion K) a - y.val ⟨.finite vi, hp⟩)‖)
              (‖y.val ⟨.finite vi, hp⟩‖) := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ max (max (‖algebraMap K (vi.adicCompletion K) z -
                  algebraMap K (vi.adicCompletion K) a‖)
                (‖algebraMap K (vi.adicCompletion K) a - y.val ⟨.finite vi, hp⟩‖))
              (‖y.val ⟨.finite vi, hp⟩‖) := by
                gcongr; exact IsUltrametricDist.norm_add_le_max _ _
          _ ≤ max (max 1 1) 1 := by gcongr
          _ = 1 := by simp
    | infinite wi =>
      have hW' := hW_nhds_y ⟨.infinite wi, hp⟩ hpT
      obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.nhds_basis_ball.mem_iff.mp hW'
      obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp (infPlace_denseRange_algebraMap wi)
        (y.val ⟨.infinite wi, hp⟩) (min ε 1 / 4) (by positivity)
      refine ⟨a, min ε 1 / 4, by positivity,
        le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)) (by norm_num),
        fun z hz => ?_, fun _ _ _ => Set.mem_univ _⟩
      apply hε_sub; rw [Metric.mem_ball]
      have h2 : dist (algebraMap K wi.Completion a)
          (algebraMap K wi.Completion z) ≤ min ε 1 / 4 := by
        rw [dist_eq_norm, ← map_sub, infPlace_norm_algebraMap]
        rwa [show wi.1 (a - z) = wi.1 (z - a) from AbsoluteValue.map_sub wi.1 a z]
      calc dist (algebraMap K wi.Completion z) (y.val ⟨.infinite wi, hp⟩)
          ≤ dist (algebraMap K wi.Completion z) (algebraMap K wi.Completion a) +
            dist (algebraMap K wi.Completion a) (y.val ⟨.infinite wi, hp⟩) :=
              dist_triangle _ _ _
        _ ≤ min ε 1 / 4 + min ε 1 / 4 := by
            have hd1 : dist (algebraMap K wi.Completion z)
                (algebraMap K wi.Completion a) ≤ min ε 1 / 4 := by
              rw [dist_comm]; exact h2
            have hd2 : dist (algebraMap K wi.Completion a)
                (y.val ⟨.infinite wi, hp⟩) ≤ min ε 1 / 4 := by
              rw [dist_comm]; linarith
            linarith
        _ ≤ ε / 4 + ε / 4 := by
            gcongr <;> exact min_le_left _ _

        _ < ε := by linarith

  choose a_fun ε_fun hε_pos hε_le_one h_in_W h_int_W using h_targets

  let mk_subtype : (p : Place K) → p ∈ S_place → {v : Place K // v ≠ w} := fun p hp =>
    ⟨p, by obtain ⟨v, _, hv_eq⟩ := Finset.mem_image.mp hp; exact hv_eq ▸ v.2⟩
  let sa_target : (p : Place K) → p ∈ S_place → K := fun p hp =>
    a_fun (mk_subtype p hp) (hval_in_T (mk_subtype p hp) hp)
  let sa_eps : (p : Place K) → p ∈ S_place → ℝ := fun p hp =>
    ε_fun (mk_subtype p hp) (hval_in_T (mk_subtype p hp) hp)
  have sa_eps_pos : ∀ p (hp : p ∈ S_place), 0 < sa_eps p hp := fun p hp =>
    hε_pos (mk_subtype p hp) (hval_in_T (mk_subtype p hp) hp)
  obtain ⟨x, hx_close, hx_out⟩ := strong_approximation S_place w hw_not_in
    sa_target sa_eps sa_eps_pos
  refine ⟨diagonalAwayFrom w x, ?_, x, rfl⟩

  have hx_int : ∀ (v : {v : Place K // v ≠ w}), v ∉ T →
      embedAtPlace v.val x ∈ placeIntegerSet v.val := by
    intro v hv_not_T
    apply placeNorm_le_one_imp_mem_placeIntegerSet
    exact hx_out v.val (fun hmem => hv_not_T (hval_in_T v hmem)) v.2

  have hx_placeNorm_bound : ∀ (v : {v : Place K // v ≠ w}) (hv : v ∈ T),
      placeNorm v.val (x - a_fun v hv) ≤ ε_fun v hv := by
    intro v hv
    have hmem_S : v.val ∈ S_place := Finset.mem_image.mpr ⟨v, hT_mem v hv, rfl⟩
    have hclose := hx_close v.val hmem_S
    have hmk : mk_subtype v.val hmem_S = v := Subtype.ext rfl
    simp only [sa_target, sa_eps, hmk] at hclose
    convert hclose using 2


  have hx_in_W : ∀ (v : {v : Place K // v ≠ w}), v ∈ T →
      embedAtPlace v.val x ∈ W v := by
    intro v hv; exact h_in_W v hv x (hx_placeNorm_bound v hv)

  have hx_int_T : ∀ (v : {v : Place K // v ≠ w}), v ∈ T → v ∈ S_y →
      embedAtPlace v.val x ∈ placeIntegerSet v.val := by
    intro v hv hv_Sy; exact h_int_W v hv hv_Sy x (hx_placeNorm_bound v hv)

  have hx_all_Sy : ∀ v ∈ S_y, embedAtPlace v.val x ∈ placeIntegerSet v.val := by
    intro v hv
    by_cases hv_T : v ∈ T
    · exact hx_int_T v hv_T hv
    · exact hx_int v hv_T

  have hfx_ev : ∀ᶠ v in Filter.principal S_y,
      (diagonalAwayFrom w x : ∀ i, placeCompletion i.val) v ∈ placeIntegerSet v.val := by
    apply Filter.eventually_principal.mpr
    intro v hv
    simp only [diagonalAwayFrom, RestrictedProduct.mk_apply]
    exact hx_all_Sy v hv

  obtain ⟨fx', hfx'_eq⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually
    (fun (v : {v : Place K // v ≠ w}) => placeCompletion v.val)
    (fun (v : {v : Place K // v ≠ w}) => placeIntegerSet v.val)
    hS_y hfx_ev

  rw [show diagonalAwayFrom w x = RestrictedProduct.inclusion _ _ hS_y fx' from hfx'_eq.symm]
  apply hV_sub
  apply hW_sub
  intro v hv
  have hfx'_val : fx' v = embedAtPlace v.val x := by
    have : (RestrictedProduct.inclusion _ _ hS_y fx').val v = (diagonalAwayFrom w x).val v :=
      congr_fun (congrArg Subtype.val hfx'_eq) v
    simp only [RestrictedProduct.inclusion, diagonalAwayFrom] at this

    exact this
  rw [hfx'_val]
  exact hx_in_W v hv

end NumberField.Adeles
