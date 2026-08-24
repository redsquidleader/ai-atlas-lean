/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Atlas.NumberTheoryI.code.CompleteFields
import Atlas.NumberTheoryI.code.KroneckerWeber

noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

namespace AbsoluteValue

variable {K : Type*} [Field K]

def IsTrivial (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x : K, x ≠ 0 → v x = 1

theorem IsTrivial.map_ne_zero {v : AbsoluteValue K ℝ} (hv : v.IsTrivial) {x : K}
    (hx : x ≠ 0) : v x = 1 :=
  hv x hx

theorem IsTrivial.of_isEquiv {v w : AbsoluteValue K ℝ} (hv : v.IsTrivial) (h : v.IsEquiv w) :
    w.IsTrivial := by
  intro x hx
  have h0 : v x = v 1 := by rw [hv x hx, map_one]
  have h1 := h.eq_iff_eq.mp h0
  rw [map_one] at h1
  exact h1

end AbsoluteValue

section Place

variable (K : Type*) [Field K]

instance nontrivialAbsValSetoid :
    Setoid { v : AbsoluteValue K ℝ // ¬v.IsTrivial } where
  r v w := v.val.IsEquiv w.val
  iseqv := {
    refl := fun _ => AbsoluteValue.IsEquiv.refl _
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def Place := Quotient (nontrivialAbsValSetoid K)

end Place

section PlaceExtension

def restrictPlace {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) : NumberField.InfinitePlace K :=
  w.comap (algebraMap K L)

def InfinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) : Prop :=
  restrictPlace w = v

def FinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal

end PlaceExtension

instance instAlgebraBaseOfExtCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    Algebra K w.Completion :=
  ((algebraMap L w.Completion).comp (algebraMap K L)).toAlgebra

instance instAlgebraBaseOfExtAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra K (w.adicCompletion L) := inferInstance

section TensorProductDecomposition

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 80000

theorem theorem_13_5_dense_embedding (K : Type*) [Field K] [NumberField K] :
    DenseRange (algebraMap K ((v : NumberField.InfinitePlace K) → WithAbs v.1)) :=
  denseRange_algebraMap_pi K

def algebraMapLToCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    L →ₐ[K] w.Completion where
  toFun := algebraMap L w.Completion
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
def completionEmbedding {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace L) (hw : w.comap (algebraMap K L) = v) :
    v.Completion →ₐ[K] w.Completion := by
  haveI : w.1.LiesOver v.1 := ⟨by
    have : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← this]; rfl⟩
  let iso := LiesOver.isometry_algebraMap w (v := v)
  let f : v.Completion →+* w.Completion := iso.mapRingHom
  exact {
    toRingHom := f
    commutes' := by
      intro r
      show f (algebraMap K v.Completion r) = algebraMap K w.Completion r
      change f (↑(algebraMap K (WithAbs v.1) r)) = ↑(algebraMap K (WithAbs w.1) r)
      rw [iso.mapRingHom_coe]
      congr 1
  }

def canonicalMap {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    TensorProduct K L v.Completion →ₐ[K]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
  Pi.algHom K
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      w.val.Completion)
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToCompletion w.val)
        (completionEmbedding v w.val w.prop))

instance nontriviallyNormedField_infinitePlace_completion {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) : NontriviallyNormedField v.Completion := by
  constructor; use 2
  have h1 : Completion.extensionEmbedding v 2 = (2 : ℂ) := by simp [map_ofNat]
  have h2 : ‖(2 : v.Completion)‖ = ‖(2 : ℂ)‖ := by
    rw [← h1]
    exact ((Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) 2).symm
  rw [h2]; norm_num

set_option backward.isDefEq.respectTransparency false in
theorem completionEmbedding_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace L) (hw : w.comap (algebraMap K L) = v) :
    Continuous (completionEmbedding v w hw) := by
  simp only [completionEmbedding, Isometry.mapRingHom, UniformSpace.Completion.mapRingHom]
  exact UniformSpace.Completion.continuous_extension

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
theorem canonicalMap_surjective_hfd_tgt {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    @FiniteDimensional v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) _ _
      (@Pi.module
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
        (fun w => w.val.Completion) v.Completion _ _
        (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)) := by


  have h_fin : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
    @Module.Finite v.Completion w.val.Completion _ _
      (completionEmbedding v w.val w.prop).toAlgebra.toModule := by
    intro w
    letI myAlg : Algebra v.Completion w.val.Completion :=
      (completionEmbedding v w.val w.prop).toAlgebra
    letI mySMul : SMul v.Completion w.val.Completion := myAlg.toSMul
    haveI : ContinuousMul w.val.Completion :=
      (inferInstance : IsTopologicalRing w.val.Completion).toContinuousMul
    haveI : @ContinuousSMul v.Completion w.val.Completion mySMul _ _ := by
      refine ⟨?_⟩
      show Continuous (fun p : v.Completion × w.val.Completion =>
        completionEmbedding v w.val w.prop p.1 * p.2)
      exact ((completionEmbedding_continuous v w.val w.prop).comp continuous_fst).mul continuous_snd
    exact @FiniteDimensional.of_locallyCompactSpace v.Completion _ _ w.val.Completion _ _ _ _
      myAlg.toModule this _

  exact @Module.Finite.pi v.Completion _
    { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
    (fun w => w.val.Completion) _
    (fun w => inferInstance)
    (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)
    h_fin

theorem degree_identity_infinite_finrank
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K)
    [Fintype { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }] :
    Module.finrank K L =
    ∑ w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v },
      @Module.finrank v.Completion w.val.Completion _ _
        (completionEmbedding v w.val w.prop).toAlgebra.toModule := by sorry

theorem canonicalMap_surjective_hdim {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    @Module.finrank v.Completion (TensorProduct K L v.Completion) _ _
      (Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)).toModule =
    @Module.finrank v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) _ _
      (@Pi.module
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
        (fun w => w.val.Completion) v.Completion _ _
        (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)) := by


  letI instTgt : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
      Module v.Completion w.val.Completion :=
    fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule

  haveI : Fintype { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } :=
    Fintype.ofFinite _

  haveI h_fin : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
      @Module.Finite v.Completion w.val.Completion _ _ (instTgt w) := by
    intro w
    letI myAlg : Algebra v.Completion w.val.Completion :=
      (completionEmbedding v w.val w.prop).toAlgebra
    letI mySMul : SMul v.Completion w.val.Completion := myAlg.toSMul
    haveI : ContinuousMul w.val.Completion :=
      (inferInstance : IsTopologicalRing w.val.Completion).toContinuousMul
    haveI : @ContinuousSMul v.Completion w.val.Completion mySMul _ _ := by
      refine ⟨?_⟩
      show Continuous (fun p : v.Completion × w.val.Completion =>
        completionEmbedding v w.val w.prop p.1 * p.2)
      exact ((completionEmbedding_continuous v w.val w.prop).comp continuous_fst).mul continuous_snd
    exact @FiniteDimensional.of_locallyCompactSpace v.Completion _ _ w.val.Completion _ _ _ _
      myAlg.toModule this _

  haveI instFree : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
      @Module.Free v.Completion w.val.Completion _ _ (instTgt w) :=
    fun w => @Module.Free.of_divisionRing _ _ _ _ (instTgt w)


  letI : Algebra v.Completion (TensorProduct K L v.Completion) :=
    Algebra.TensorProduct.rightAlgebra
  have h_lhs : Module.finrank v.Completion (TensorProduct K L v.Completion) =
      Module.finrank K L := by
    have h1 := LinearEquiv.finrank_eq
      (Algebra.TensorProduct.commRight K v.Completion L).symm.toLinearEquiv
    rw [h1]
    exact Module.finrank_baseChange ..

  have h_rhs : @Module.finrank v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) _ _
      (@Pi.module
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
        (fun w => w.val.Completion) v.Completion _ _
        (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)) =
      ∑ w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v },
        @Module.finrank v.Completion w.val.Completion _ _ (instTgt w) :=
    @Module.finrank_pi_fintype v.Completion _ _ _ _ _ _ instTgt instFree h_fin

  have h_bridge := degree_identity_infinite_finrank (L := L) v
  linarith

set_option maxHeartbeats 800000 in
theorem canonicalMap_injective {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Function.Injective (canonicalMap (L := L) v) := by

  letI instSrc : Module v.Completion (TensorProduct K L v.Completion) :=
    (Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)).toModule
  letI instTgt : Module v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
    @Pi.module
      { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
      (fun w => w.val.Completion) v.Completion _ _
      (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)

  have hfd_src : FiniteDimensional v.Completion (TensorProduct K L v.Completion) := by
    letI : Algebra v.Completion (TensorProduct K L v.Completion) :=
      Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
    haveI : Module.Finite v.Completion (TensorProduct K v.Completion L) :=
      Module.Finite.base_change K v.Completion L
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  have hfd_tgt : FiniteDimensional v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) := canonicalMap_surjective_hfd_tgt v

  have hdim : Module.finrank v.Completion (TensorProduct K L v.Completion) =
      Module.finrank v.Completion
        ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
          w.val.Completion) := canonicalMap_surjective_hdim v

  have hsmul : ∀ (c : v.Completion) (x : TensorProduct K L v.Completion),
      (canonicalMap (L := L) v) (c • x) =
        @SMul.smul _ _ instTgt.toSMul c ((canonicalMap (L := L) v) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [smul_zero, map_zero]
      exact (@smul_zero _ _ _
        instTgt.toDistribMulAction.toDistribSMul.toSMulZeroClass c).symm
    | tmul l y =>
      change (canonicalMap (L := L) v) ((1 ⊗ₜ c) * (l ⊗ₜ y)) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      ext ⟨w, hw⟩
      simp only [canonicalMap, Pi.algHom_apply,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact mul_left_comm _ _ _
    | add a b ha hb =>
      simp only [smul_add, map_add, ha, hb]
      exact (@smul_add _ _ _
        instTgt.toDistribMulAction.toDistribSMul c
        ((canonicalMap v) a) ((canonicalMap v) b)).symm

  let f : TensorProduct K L v.Completion →ₗ[v.Completion]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
    { toFun := canonicalMap v
      map_add' := (canonicalMap v).map_add
      map_smul' := hsmul }


  have h_dense_diag : DenseRange
      (fun (ℓ : L) (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
        algebraMap L w.val.Completion ℓ) := by
    let proj : NumberField.InfiniteAdeleRing L →
        ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
          w.val.Completion) :=
      fun x w => x w.val
    have h_proj_cont : Continuous proj := continuous_pi (fun w => continuous_apply w.val)
    have h_proj_surj : Function.Surjective proj := by
      intro y
      classical
      exact ⟨fun w => if h : w.comap (algebraMap K L) = v then
        y ⟨w, h⟩ else 0, by ext ⟨w, hw⟩; simp [proj, hw]⟩
    have h_dense_all := NumberField.InfiniteAdeleRing.denseRange_algebraMap L
    have h_comp : DenseRange (proj ∘ algebraMap L (NumberField.InfiniteAdeleRing L)) :=
      h_proj_surj.denseRange.comp h_dense_all h_proj_cont
    convert h_comp using 1

  have h_range_dense : Dense (Set.range f) := by
    apply h_dense_diag.mono
    rintro y ⟨ℓ, rfl⟩
    exact ⟨ℓ ⊗ₜ[K] 1, by
      ext ⟨w, hw⟩
      show (canonicalMap v) (ℓ ⊗ₜ[K] 1) ⟨w, hw⟩ = (algebraMap L w.Completion) ℓ
      simp only [canonicalMap, Pi.algHom_apply,
        Algebra.TensorProduct.productMap_apply_tmul, map_one,
        algebraMapLToCompletion]
      exact mul_one _⟩

  haveI : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
      @ContinuousSMul v.Completion w.val.Completion
        ((completionEmbedding v w.val w.prop).toAlgebra.toSMul) _ _ := by
    intro w
    letI mySMul : SMul v.Completion w.val.Completion :=
      (completionEmbedding v w.val w.prop).toAlgebra.toSMul
    haveI : ContinuousMul w.val.Completion :=
      (inferInstance : IsTopologicalRing w.val.Completion).toContinuousMul
    exact ⟨by
      show Continuous (fun p : v.Completion × w.val.Completion =>
        completionEmbedding v w.val w.prop p.1 * p.2)
      exact ((completionEmbedding_continuous v w.val w.prop).comp continuous_fst).mul continuous_snd⟩


  have h_range_closed : IsClosed (Set.range f) := by
    have : IsClosed (SetLike.coe (LinearMap.range f)) :=
      Submodule.closed_of_finiteDimensional _
    convert this using 1

  have hsurj : Function.Surjective f := by
    intro y
    have h1 : closure (Set.range f) = Set.univ := h_range_dense.closure_eq
    have h2 : closure (Set.range f) = Set.range f := h_range_closed.closure_eq
    exact (h2 ▸ h1 ▸ Set.mem_univ y : y ∈ Set.range f)

  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj

theorem canonicalMap_surjective {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Function.Surjective (canonicalMap (L := L) v) := by

  letI instSrc : Module v.Completion (TensorProduct K L v.Completion) :=
    (Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)).toModule

  letI instTgt : Module v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
    @Pi.module
      { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
      (fun w => w.val.Completion) v.Completion _ _
      (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)

  have hfd_src : FiniteDimensional v.Completion (TensorProduct K L v.Completion) := by
    letI : Algebra v.Completion (TensorProduct K L v.Completion) :=
      Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
    haveI : Module.Finite v.Completion (TensorProduct K v.Completion L) :=
      Module.Finite.base_change K v.Completion L
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  have hfd_tgt : FiniteDimensional v.Completion
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) := canonicalMap_surjective_hfd_tgt v

  have hdim : Module.finrank v.Completion (TensorProduct K L v.Completion) =
      Module.finrank v.Completion
        ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
          w.val.Completion) := canonicalMap_surjective_hdim v

  have hsmul : ∀ (c : v.Completion) (x : TensorProduct K L v.Completion),
      (canonicalMap (L := L) v) (c • x) =
        @SMul.smul _ _ instTgt.toSMul c ((canonicalMap (L := L) v) x) := by
    intro c x

    induction x using TensorProduct.induction_on with
    | zero =>
      rw [smul_zero, map_zero]
      exact (@smul_zero _ _ _
        instTgt.toDistribMulAction.toDistribSMul.toSMulZeroClass c).symm
    | tmul l y =>

      change (canonicalMap (L := L) v) ((1 ⊗ₜ c) * (l ⊗ₜ y)) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      ext ⟨w, hw⟩
      simp only [canonicalMap, Pi.algHom_apply,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact mul_left_comm _ _ _
    | add a b ha hb =>
      simp only [smul_add, map_add, ha, hb]
      exact (@smul_add _ _ _
        instTgt.toDistribMulAction.toDistribSMul c
        ((canonicalMap v) a) ((canonicalMap v) b)).symm

  let f : TensorProduct K L v.Completion →ₗ[v.Completion]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
    { toFun := canonicalMap v
      map_add' := (canonicalMap v).map_add
      map_smul' := hsmul }

  have hinj : Function.Injective f := canonicalMap_injective v

  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

theorem canonicalMap_bijective {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Function.Bijective (canonicalMap (L := L) v) :=
  ⟨canonicalMap_injective v, canonicalMap_surjective v⟩

noncomputable def canonicalMapEquiv {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    TensorProduct K L v.Completion ≃+*
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
  RingEquiv.ofBijective (canonicalMap v).toRingHom (canonicalMap_bijective v)

theorem canonicalMap_tmul_one {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) (l : L)
    (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) :
    (canonicalMap (L := L) v) (l ⊗ₜ[K] 1) w = algebraMap L w.val.Completion l := by
  simp only [canonicalMap, Pi.algHom_apply,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, algebraMapLToCompletion]
  exact mul_one _

set_option maxHeartbeats 8000000

theorem theorem_13_5_tensor_product_iso {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (v : NumberField.InfinitePlace K) :
    Nonempty (TensorProduct K L v.Completion ≃ₐ[K]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion)) :=
  ⟨AlgEquiv.ofBijective (canonicalMap v)
    ⟨canonicalMap_injective v, canonicalMap_surjective v⟩⟩

theorem theorem_13_5_tensor_product_iso_Kv {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (v : NumberField.InfinitePlace K) :
    Nonempty (
      letI : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
        Algebra v.Completion w.val.Completion :=
        fun w => (completionEmbedding v w.val w.prop).toAlgebra
      @AlgEquiv v.Completion
        (TensorProduct K L v.Completion)
        ((ω : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
          ω.val.Completion)
        _ _ _ (Algebra.TensorProduct.rightAlgebra) (Pi.algebra _ _)) := by

  letI inst_Kv_src : Algebra v.Completion (TensorProduct K L v.Completion) :=
    Algebra.TensorProduct.rightAlgebra
  letI inst_Kv_tgt : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
      Algebra v.Completion w.val.Completion :=
    fun w => (completionEmbedding v w.val w.prop).toAlgebra

  let e_K := AlgEquiv.ofBijective (canonicalMap (L := L) v)
    ⟨canonicalMap_injective v, canonicalMap_surjective v⟩

  let f : TensorProduct K L v.Completion ≃+*
      ((ω : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        ω.val.Completion) := e_K.toRingEquiv

  have hf_alg : ∀ (x : v.Completion),
      f (algebraMap v.Completion (TensorProduct K L v.Completion) x) =
        algebraMap v.Completion
          ((ω : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
            ω.val.Completion) x := by
    intro x
    ext w
    change e_K (Algebra.TensorProduct.includeRight (R := K) x) w = _
    simp only [e_K, AlgEquiv.ofBijective_apply, canonicalMap, Pi.algHom_apply,
      Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeRight_apply,
      algebraMapLToCompletion, map_one, Pi.algebraMap_apply]
    erw [one_mul]
    rfl

  exact ⟨@AlgEquiv.ofRingEquiv v.Completion _ _ _ _ _ inst_Kv_src (Pi.algebra _ _)
    (f := f) hf_alg⟩

def completionEmbedding_finite_ringHom {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) :
    WithVal (v.valuation K) →+* w.adicCompletion L :=
  (algebraMap K (w.adicCompletion L)).comp (WithVal.equiv (v.valuation K)).toRingHom


lemma multiplicative_toAdd_pow (h : Multiplicative ℤ) (e : ℕ) :
    Multiplicative.toAdd (h ^ e) = e * Multiplicative.toAdd h := by
  induction e with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_mul, one_mul]


lemma exists_pow_lt_of_ne_zero (m : WithZero (Multiplicative ℤ)) (hm : m ≠ 0)
    (e : ℕ) (he : e ≠ 0) :
    ∃ d : WithZero (Multiplicative ℤ), d ≠ 0 ∧ ∀ a : WithZero (Multiplicative ℤ),
      a < d → a ^ e < m := by
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hm
  set n := Multiplicative.toAdd g
  use ↑(Multiplicative.ofAdd (n / (e : ℤ)))
  refine ⟨WithZero.coe_ne_zero, fun a ha => ?_⟩
  cases a with
  | zero => rw [zero_pow he]; exact WithZero.zero_lt_coe g
  | coe h =>
    rw [WithZero.coe_lt_coe] at ha
    rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
    suffices (e : ℤ) * Multiplicative.toAdd h < n by
      rwa [show h ^ e < g ↔ Multiplicative.toAdd (h ^ e) < n from Iff.rfl,
           multiplicative_toAdd_pow]
    have he_pos : (0 : ℤ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
    have hle : Multiplicative.toAdd h ≤ n / (e : ℤ) - 1 :=
      Int.le_sub_one_of_lt ha
    calc (e : ℤ) * Multiplicative.toAdd h
        ≤ (e : ℤ) * (n / (e : ℤ) - 1) := mul_le_mul_of_nonneg_left hle he_pos.le
      _ = (e : ℤ) * (n / (e : ℤ)) - (e : ℤ) := by ring
      _ ≤ n - 1 := by linarith [Int.ediv_mul_le n he_pos.ne']
      _ < n := by omega

set_option maxHeartbeats 1600000 in
theorem algebraMap_withVal_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.LiesAbove w v) :
    Continuous
      ((WithVal.equiv (w.valuation L)).symm.toRingHom.comp
        ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom) :
        WithVal (v.valuation K) →+* WithVal (w.valuation L)) := by

  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩

  have hval : ∀ x : K, w.valuation L (algebraMap K L x) =
      (v.valuation K x) ^ (Ideal.ramificationIdx v.asIdeal w.asIdeal) :=
    fun x => valuation_extends_with_ramificationIdx K L v w x
  let e := Ideal.ramificationIdx v.asIdeal w.asIdeal
  have he : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot

  let f : WithVal (v.valuation K) →+* WithVal (w.valuation L) :=
    (WithVal.equiv (w.valuation L)).symm.toRingHom.comp
      ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom)
  show Continuous f

  have hfv : ∀ x : WithVal (v.valuation K),
      @Valued.v (WithVal (w.valuation L)) _ _ _ _ (f x) =
      (@Valued.v (WithVal (v.valuation K)) _ _ _ _ x) ^ e := by
    intro x
    rw [← WithVal.val_apply_equiv (w.valuation L)]
    show w.valuation L ((WithVal.equiv (w.valuation L)) ((WithVal.equiv (w.valuation L)).symm
      (algebraMap K L ((WithVal.equiv (v.valuation K)) x)))) = _
    rw [RingEquiv.apply_symm_apply, hval, ← WithVal.val_apply_equiv (v.valuation K)]

  apply continuous_of_continuousAt_zero f.toAddMonoidHom
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]

  intro γ


  set M := MonoidWithZeroHom.ValueGroup₀.embedding (↑γ : MonoidWithZeroHom.ValueGroup₀
    (@Valued.v (WithVal (w.valuation L)) _ _ _ _)) with hM_def
  have hM_ne : M ≠ 0 := by
    simp only [M, ne_eq, map_eq_zero]
    exact Units.ne_zero γ

  obtain ⟨d, hd_ne, hd_pow⟩ := exists_pow_lt_of_ne_zero M hM_ne e he


  obtain ⟨y, hy⟩ := v.valuation_surjective K d

  set y' : WithVal (v.valuation K) := (WithVal.equiv (v.valuation K)).symm y with hy'_def

  set δ_vg := MonoidWithZeroHom.ValueGroup₀.restrict₀
    (@Valued.v (WithVal (v.valuation K)) _ _ _ _) y' with hδ_vg_def

  have hδ_emb : MonoidWithZeroHom.ValueGroup₀.embedding δ_vg = d := by
    rw [hδ_vg_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    show @Valued.v (WithVal (v.valuation K)) _ _ _ _ y' = d
    rw [← WithVal.val_apply_equiv (v.valuation K), hy'_def]
    simp [hy]

  have hδ_ne : δ_vg ≠ 0 := by
    intro h; rw [h, map_zero] at hδ_emb; exact hd_ne hδ_emb.symm
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact hd_ne hy.symm

  set y'_inv : WithVal (v.valuation K) := (WithVal.equiv (v.valuation K)).symm y⁻¹
  have hδ_unit : IsUnit δ_vg := by
    rw [isUnit_iff_exists_inv]
    use MonoidWithZeroHom.ValueGroup₀.restrict₀
      (@Valued.v (WithVal (v.valuation K)) _ _ _ _) y'_inv
    rw [← map_mul]
    have : y' * y'_inv = 1 := by
      show (WithVal.equiv (v.valuation K)).symm y *
        (WithVal.equiv (v.valuation K)).symm y⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    rw [this, map_one]
  obtain ⟨δ, hδ⟩ := hδ_unit
  use δ
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢

  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢


  rw [hδ, hδ_emb] at hx

  change @Valued.v (WithVal (w.valuation L)) _ _ _ _ (f x) < M

  rw [hfv]

  exact hd_pow _ hx

theorem completionEmbedding_finite_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    Continuous (completionEmbedding_finite_ringHom v w) := by


  let g : WithVal (v.valuation K) → WithVal (w.valuation L) :=
    fun x => (WithVal.equiv (w.valuation L)).symm
      (algebraMap K L ((WithVal.equiv (v.valuation K)) x))
  have hg : Continuous g := algebraMap_withVal_continuous v w hw
  have hcoe : Continuous (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) :=
    (UniformSpace.Completion.uniformContinuous_coe _).continuous
  have heq : (completionEmbedding_finite_ringHom v w : WithVal (v.valuation K) → w.adicCompletion L) =
      (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) ∘ g := by
    funext x
    simp only [g, completionEmbedding_finite_ringHom, Function.comp, RingHom.coe_comp,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [show (↑(completionEmbedding_finite_ringHom v w) :
    WithVal (v.valuation K) → w.adicCompletion L) =
    (fun x : WithVal (w.valuation L) => (↑x : w.adicCompletion L)) ∘ g from heq]
  exact hcoe.comp hg

def completionEmbedding_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    v.adicCompletion K →ₐ[K] w.adicCompletion L :=
  AlgHom.mk'
    (UniformSpace.Completion.extensionHom
      (completionEmbedding_finite_ringHom v w)
      (completionEmbedding_finite_continuous v w hw))
    (fun k x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      show (UniformSpace.Completion.extensionHom
        (completionEmbedding_finite_ringHom v w)
        (completionEmbedding_finite_continuous v w hw))
        (algebraMap K (v.adicCompletion K) k) =
        algebraMap K (w.adicCompletion L) k
      have : algebraMap K (v.adicCompletion K) k =
        (↑(algebraMap K (WithVal (v.valuation K)) k) : v.adicCompletion K) := rfl
      rw [this, UniformSpace.Completion.extensionHom_coe]
      rfl)

def algebraMapLToAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    L →ₐ[K] w.adicCompletion L where
  toFun := algebraMap L (w.adicCompletion L)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

def canonicalMap_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    TensorProduct K L (v.adicCompletion K) →ₐ[K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) :=
  Pi.algHom K
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      w.val.adicCompletion L)
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToAdicCompletion w.val)
        (completionEmbedding_finite v w.val w.prop))

set_option synthInstance.maxHeartbeats 80000 in
theorem prop_4_36_tensorProduct_finite_isSemisimpleRing
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsSemisimpleRing (TensorProduct K L (v.adicCompletion K)) := by

  haveI : Algebra.Unramified K L :=
    ⟨Algebra.FormallyUnramified.of_isSeparable K L, inferInstance⟩

  haveI := (Algebra.Unramified.baseChange K L (v.adicCompletion K)).formallyUnramified

  haveI : IsReduced (TensorProduct K (v.adicCompletion K) L) :=
    Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion K) _

  haveI : IsArtinianRing (TensorProduct K (v.adicCompletion K) L) :=
    IsArtinianRing.of_finite (v.adicCompletion K) _

  haveI : IsSemisimpleRing (TensorProduct K (v.adicCompletion K) L) :=
    @IsArtinianRing.isSemisimpleRing_of_isReduced _ _ _ _

  exact (Algebra.TensorProduct.comm K L (v.adicCompletion K)).toRingEquiv.symm.isSemisimpleRing

theorem finitePlacesAbove_finite
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } := by
  haveI := v.isMaximal
  apply Finite.of_injective
    (fun ⟨w, hw⟩ => (⟨w.asIdeal, w.isPrime, ⟨hw.symm⟩⟩ : Ideal.primesOver v.asIdeal (𝓞 L)))
  intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (HeightOneSpectrum.ext_iff.mpr h)

theorem prop_10_3_10_4_finiteDimensional_completion
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    letI := (completionEmbedding_finite v w hw).toAlgebra
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := by
  letI := (completionEmbedding_finite v w hw).toAlgebra
  haveI : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    show Continuous (completionEmbedding_finite v w hw).toRingHom
    exact UniformSpace.Completion.continuous_extension
  haveI : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap K (w.adicCompletion L) x =
      (completionEmbedding_finite v w hw) (algebraMap K (v.adicCompletion K) x)
    rw [AlgHom.commutes]
  exact inferInstance

theorem thm_11_23_4_local_degree_ef
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.LiesAbove w v)
    [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
    Ideal.ramificationIdx v.asIdeal w.asIdeal *
    Ideal.inertiaDeg v.asIdeal w.asIdeal := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  exact KroneckerWeber.thm_11_23_part4_completion_degree_eq_ef
    (𝓞 K) K L (𝓞 L) v w

theorem thm_5_35_11_23_degree_identity_finrank
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (instAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
        Algebra (v.adicCompletion K) (w.val.adicCompletion L))
    (instST : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
        @IsScalarTower K (v.adicCompletion K) (w.val.adicCompletion L) _
          (instAlg w).toSMul _) :
    Module.finrank K L =
    ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.finrank (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (instAlg w).toModule := by

  have h_ef : ∀ (ww : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      @Module.finrank (v.adicCompletion K) (ww.val.adicCompletion L) _ _
        (instAlg ww).toModule =
      Ideal.ramificationIdx v.asIdeal ww.val.asIdeal *
      Ideal.inertiaDeg v.asIdeal ww.val.asIdeal := by
    intro ⟨w, hw⟩
    exact @thm_11_23_4_local_degree_ef K L _ _ _ _ _ _ _ v w hw
      (instAlg ⟨w, hw⟩) (instST ⟨w, hw⟩)
  simp_rw [h_ef]

  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  rw [← Ideal.sum_ramification_inertia (𝓞 L) K L v.ne_bot]

  symm
  apply Finset.sum_nbij
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) => w.val.asIdeal)
  ·
    intro ⟨w, hw⟩ _
    rw [mem_primesOverFinset_iff v.ne_bot]
    exact ⟨w.isPrime, ⟨(show FinitePlace.LiesAbove w v from hw).symm⟩⟩
  ·
    intro ⟨w₁, _⟩ _ ⟨w₂, _⟩ _ h
    simp only [Subtype.mk.injEq]
    exact HeightOneSpectrum.ext h
  ·
    intro P hP
    simp only [Finset.coe_univ, Set.mem_univ, Finset.mem_coe, Set.mem_image, true_and] at hP ⊢
    rw [mem_primesOverFinset_iff v.ne_bot] at hP
    have hne : P ≠ ⊥ := by
      intro h; rw [h] at hP
      have := hP.2.over
      simp only [Ideal.under] at this
      rw [Ideal.comap_bot_of_injective _
        (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L)] at this
      exact v.ne_bot this
    exact ⟨⟨⟨P, hP.1, hne⟩, (show FinitePlace.LiesAbove ⟨P, hP.1, hne⟩ v from hP.2.over.symm)⟩, rfl⟩
  ·
    intro _ _; rfl

theorem prop_10_3_10_4_finrank_eq
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
      Algebra.TensorProduct.rightAlgebra
    letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
        Module (v.adicCompletion K) (w.val.adicCompletion L) :=
      fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
    Module.finrank (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) =
    Module.finrank (v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) := by

  letI instSrc : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI instTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra


  haveI hfin : Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } :=
    finitePlacesAbove_finite v
  haveI : Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } :=
    Fintype.ofFinite _

  haveI instFD : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      @FiniteDimensional (v.adicCompletion K) (w.val.adicCompletion L) _ _ (instTgt w).toModule :=
    fun w => prop_10_3_10_4_finiteDimensional_completion v w.val w.prop

  haveI instFree : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _ (instTgt w).toModule :=
    fun w => @Module.Free.of_divisionRing _ _ _ _ (instTgt w).toModule


  have h_lhs : Module.finrank (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) =
      Module.finrank K L := by
    have := LinearEquiv.finrank_eq
      (Algebra.TensorProduct.commRight K (v.adicCompletion K) L).symm.toLinearEquiv
    rw [this]
    exact Module.finrank_baseChange ..

  have h_rhs : Module.finrank (v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) =
      ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
        Module.finrank (v.adicCompletion K) (w.val.adicCompletion L) :=
    Module.finrank_pi_fintype (v.adicCompletion K)

  have instSTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      @IsScalarTower K (v.adicCompletion K) (w.val.adicCompletion L) _
        (instTgt w).toSMul _ :=
    fun w => IsScalarTower.of_algHom (completionEmbedding_finite v w.val w.prop)
  have h_bridge := thm_5_35_11_23_degree_identity_finrank (L := L) v instTgt instSTgt
  linarith

theorem canonicalMap_finite_isKvLinear
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
      Algebra.TensorProduct.rightAlgebra
    letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
        Module (v.adicCompletion K) (w.val.adicCompletion L) :=
      fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
    ∃ f : TensorProduct K L (v.adicCompletion K) →ₗ[v.adicCompletion K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L),
      (∀ x, f x = (canonicalMap_finite (L := L) v) x) := by
  letI instSrc : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI instTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Module (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
  letI instPiMod : Module (v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) :=
    @Pi.module _ (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      w.val.adicCompletion L) (v.adicCompletion K) _ _ instTgt
  have hsmul : ∀ (c : v.adicCompletion K) (x : TensorProduct K L (v.adicCompletion K)),
    (canonicalMap_finite (L := L) v) (c • x) =
      @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * 0) = _
      rw [mul_zero, map_zero]
      exact (@smul_zero _ _ _
        instPiMod.toDistribMulAction.toDistribSMul.toSMulZeroClass c).symm

    | tmul l y =>
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * (l ⊗ₜ y)) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      ext ⟨w, hw⟩
      simp only [canonicalMap_finite, Pi.algHom_apply,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact mul_left_comm _ _ _
    | add a b ha hb =>
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * (a + b)) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) (a + b))
      rw [mul_add, map_add, map_add]
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * a) +
        (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * b) =
        @SMul.smul _ _ instPiMod.toSMul c
          ((canonicalMap_finite (L := L) v) a + (canonicalMap_finite (L := L) v) b)
      rw [show (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * a) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) a) from ha,
        show (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * b) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) b) from hb]
      exact (@smul_add _ _ _
        instPiMod.toDistribMulAction.toDistribSMul c
        ((canonicalMap_finite v) a) ((canonicalMap_finite v) b)).symm
  exact ⟨{ toFun := canonicalMap_finite v
           map_add' := (canonicalMap_finite v).map_add
           map_smul' := hsmul }, fun _ => rfl⟩


theorem canonicalMap_finite_ker_eq_bot
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    RingHom.ker (canonicalMap_finite (L := L) v) = ⊥ := by sorry

theorem canonicalMap_finite_surjective_by_approx
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (canonicalMap_finite (L := L) v) := by

  letI inst_src : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI inst_tgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Module (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule

  haveI hfd_src : FiniteDimensional (v.adicCompletion K)
      (TensorProduct K L (v.adicCompletion K)) := by
    have := Module.Finite.base_change K (v.adicCompletion K) L
    exact Module.Finite.equiv
      (Algebra.TensorProduct.commRight K (v.adicCompletion K) L).toLinearEquiv

  haveI : Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } :=
    finitePlacesAbove_finite v
  haveI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      FiniteDimensional (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => prop_10_3_10_4_finiteDimensional_completion v w.val w.prop
  haveI hfd_tgt : FiniteDimensional (v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) := Module.Finite.pi

  have h_finrank := prop_10_3_10_4_finrank_eq (L := L) v

  obtain ⟨f_lin, hf_eq⟩ := canonicalMap_finite_isKvLinear (L := L) v

  have h_inj_lin : Function.Injective f_lin := by
    intro x y hxy
    have hinj : Function.Injective (canonicalMap_finite (L := L) v) :=
      (RingHom.injective_iff_ker_eq_bot _).mpr (canonicalMap_finite_ker_eq_bot v)
    apply hinj; rw [← hf_eq x, ← hf_eq y]; exact hxy

  have h_surj_lin : Function.Surjective f_lin := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank]
  intro x
  obtain ⟨y, hy⟩ := h_surj_lin x
  exact ⟨y, by rw [← hf_eq y]; exact hy⟩

theorem cor_4_32_no_nonzero_idempotent_in_ker_finite
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (e : TensorProduct K L (v.adicCompletion K))
    (he_idem : IsIdempotentElem e)
    (he_ker : (canonicalMap_finite (L := L) v) e = 0) :
    e = 0 := by

  letI instSrc : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI instTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Module (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule

  haveI hfd_src : FiniteDimensional (v.adicCompletion K)
      (TensorProduct K L (v.adicCompletion K)) := by
    have := Module.Finite.base_change K (v.adicCompletion K) L
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight K (v.adicCompletion K) L).toLinearEquiv
  haveI : Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } :=
    finitePlacesAbove_finite v
  haveI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      FiniteDimensional (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => prop_10_3_10_4_finiteDimensional_completion v w.val w.prop
  haveI hfd_tgt : FiniteDimensional (v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) := Module.Finite.pi

  have h_finrank := prop_10_3_10_4_finrank_eq (L := L) v
  obtain ⟨f_lin, hf_eq⟩ := canonicalMap_finite_isKvLinear (L := L) v

  have h_surj : Function.Surjective (canonicalMap_finite (L := L) v) :=
    canonicalMap_finite_surjective_by_approx v

  have h_surj_lin : Function.Surjective f_lin := by
    intro y
    obtain ⟨x, hx⟩ := h_surj y
    exact ⟨x, by rw [hf_eq x]; exact hx⟩

  have h_inj_lin : Function.Injective f_lin := by
    rwa [LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank]

  have h_inj : Function.Injective (canonicalMap_finite (L := L) v) := by
    intro x y hxy
    apply h_inj_lin
    rw [hf_eq x, hf_eq y]
    exact hxy

  exact h_inj (he_ker.trans (map_zero (canonicalMap_finite (L := L) v)).symm)

theorem canonicalMap_finite_injective {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (canonicalMap_finite (L := L) v) := by
  haveI := prop_4_36_tensorProduct_finite_isSemisimpleRing (L := L) v
  rw [RingHom.injective_iff_ker_eq_bot (f := (canonicalMap_finite (L := L) v))]
  obtain ⟨e, he_idem, he_ker⟩ :=
    IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker (canonicalMap_finite (L := L) v))
  have he_zero : e = 0 := by
    apply cor_4_32_no_nonzero_idempotent_in_ker_finite v e he_idem
    exact RingHom.mem_ker.mp (he_ker ▸ Ideal.subset_span (Set.mem_singleton e))
  rw [he_ker, he_zero]
  simp

theorem canonicalMap_finite_surjective {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (canonicalMap_finite (L := L) v) := by

  letI inst_src : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI inst_tgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Module (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule

  haveI hfd_src : FiniteDimensional (v.adicCompletion K)
      (TensorProduct K L (v.adicCompletion K)) := by
    have := Module.Finite.base_change K (v.adicCompletion K) L
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight K (v.adicCompletion K) L).toLinearEquiv

  haveI : Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } :=
    finitePlacesAbove_finite v
  haveI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      FiniteDimensional (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => prop_10_3_10_4_finiteDimensional_completion v w.val w.prop
  haveI hfd_tgt : FiniteDimensional (v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) := Module.Finite.pi

  have h_finrank := prop_10_3_10_4_finrank_eq (L := L) v

  obtain ⟨f_lin, hf_eq⟩ := canonicalMap_finite_isKvLinear (L := L) v


  have h_inj_lin : Function.Injective f_lin := by
    intro x y hxy

    suffices hinj : Function.Injective (canonicalMap_finite (L := L) v) by
      apply hinj
      rw [← hf_eq x, ← hf_eq y]
      exact hxy

    haveI := prop_4_36_tensorProduct_finite_isSemisimpleRing (L := L) v
    rw [RingHom.injective_iff_ker_eq_bot (f := (canonicalMap_finite (L := L) v))]
    obtain ⟨e, he_idem, he_ker⟩ :=
      IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker (canonicalMap_finite (L := L) v))
    have he_zero : e = 0 := by
      apply cor_4_32_no_nonzero_idempotent_in_ker_finite v e he_idem
      exact RingHom.mem_ker.mp (he_ker ▸ Ideal.subset_span (Set.mem_singleton e))
    rw [he_ker, he_zero]
    simp

  have h_surj_lin : Function.Surjective f_lin := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank]

  intro x
  obtain ⟨y, hy⟩ := h_surj_lin x
  exact ⟨y, by rw [← hf_eq y]; exact hy⟩

theorem theorem_13_5_finite_place {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (TensorProduct K L (v.adicCompletion K) ≃ₐ[K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L)) :=
  ⟨AlgEquiv.ofBijective (canonicalMap_finite v)
    ⟨canonicalMap_finite_injective v, canonicalMap_finite_surjective v⟩⟩

theorem theorem_13_5_finite_place_Kv {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ e : (
      letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
        Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
        fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra
      @AlgEquiv (v.adicCompletion K)
        (TensorProduct K L (v.adicCompletion K))
        ((ω : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
          ω.val.adicCompletion L)
        _ _ _ (Algebra.TensorProduct.rightAlgebra) (Pi.algebra _ _)),
    ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w =
        algebraMap L (w.val.adicCompletion L) α := by

  letI inst_Kv_src : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI inst_Kv_tgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra

  let e_K := AlgEquiv.ofBijective (canonicalMap_finite (L := L) v)
    ⟨canonicalMap_finite_injective v, canonicalMap_finite_surjective v⟩

  let f : TensorProduct K L (v.adicCompletion K) ≃+*
      ((ω : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        ω.val.adicCompletion L) := e_K.toRingEquiv

  have hf_alg : ∀ (x : v.adicCompletion K),
      f (algebraMap (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) x) =
        algebraMap (v.adicCompletion K)
          ((ω : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
            ω.val.adicCompletion L) x := by
    intro x


    ext w

    change e_K (Algebra.TensorProduct.includeRight (R := K) x) w = _
    simp only [e_K, AlgEquiv.ofBijective_apply, canonicalMap_finite, Pi.algHom_apply,
      Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeRight_apply,
      algebraMapLToAdicCompletion, map_one, one_mul]
    rfl

  refine ⟨@AlgEquiv.ofRingEquiv (v.adicCompletion K) _ _ _ _ _ inst_Kv_src (Pi.algebra _ _)
    (f := f) hf_alg, ?_⟩

  intro α w

  show (@AlgEquiv.ofRingEquiv (v.adicCompletion K) _ _ _ _ _ inst_Kv_src (Pi.algebra _ _)
    (f := f) hf_alg) (α ⊗ₜ[K] (1 : v.adicCompletion K)) w =
    algebraMap L (w.val.adicCompletion L) α
  rw [AlgEquiv.ofRingEquiv_apply]


  show e_K (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α
  simp only [e_K, AlgEquiv.ofBijective_apply, canonicalMap_finite, Pi.algHom_apply,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  rfl

theorem completion_real_ringEquiv {K : Type*} [Field K]
    {w : NumberField.InfinitePlace K} (hw : w.IsReal) :
    Nonempty (w.Completion ≃+* ℝ) :=
  ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw⟩

theorem completion_complex_ringEquiv {K : Type*} [Field K]
    {w : NumberField.InfinitePlace K} (hw : w.IsComplex) :
    Nonempty (w.Completion ≃+* ℂ) :=
  ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw⟩

end TensorProductDecomposition

section IrreducibleFactorsAndPlaces

open Polynomial UniqueFactorizationMonoid Classical

def factors_equiv_infinitePlace
    (K : Type*) [Field K] [NumberField K]
    (α : K) (hα : Algebra.adjoin ℚ ({α} : Set K) = ⊤)
    (v : NumberField.InfinitePlace ℚ)
    (hiso : Nonempty (TensorProduct ℚ K v.Completion ≃ₐ[ℚ]
      ((w : { w : NumberField.InfinitePlace K // w.comap (algebraMap ℚ K) = v }) →
        w.val.Completion))) :
    Fin (Multiset.card (normalizedFactors
      (Polynomial.map (algebraMap ℚ ℝ) (minpoly ℚ α)))) ≃
    NumberField.InfinitePlace K := by
  sorry

def factors_equiv_places_above_real
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : NumberField.InfinitePlace K) (hv : v.IsReal)
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hiso : Nonempty (TensorProduct K L v.Completion ≃ₐ[K]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion))) :
    Fin (Multiset.card (normalizedFactors
      (Polynomial.map
        ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom.comp
          (algebraMap K v.Completion))
        (minpoly K α)))) ≃
    { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } := by
  sorry

def deg_equiv_places_above_complex
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex)
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hiso : Nonempty (TensorProduct K L v.Completion ≃ₐ[K]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion))) :
    Fin (finrank K L) ≃
    { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } := by
  sorry

theorem corollary_13_6_factor_count (K : Type*) [Field K] [NumberField K] :
    Fintype.card (NumberField.InfinitePlace K) =
      nrRealPlaces K + nrComplexPlaces K :=
  card_eq_nrRealPlaces_add_nrComplexPlaces K

theorem corollary_13_6_irred_factors
    (K : Type*) [Field K] [NumberField K]
    (α : K) (hα : Algebra.adjoin ℚ ({α} : Set K) = ⊤) :
    Multiset.card (normalizedFactors
      (Polynomial.map (algebraMap ℚ ℝ) (minpoly ℚ α))) =
    Fintype.card (NumberField.InfinitePlace K) := by
  let v : NumberField.InfinitePlace ℚ := (inferInstance : Nonempty _).some
  have h := Fintype.card_congr (factors_equiv_infinitePlace K α hα v
    (theorem_13_5_tensor_product_iso (L := K) v))
  simp only [Fintype.card_fin] at h
  exact h

theorem corollary_13_6_places_above_real
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : NumberField.InfinitePlace K) (hv : v.IsReal)
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤) :
    (Finset.univ.filter (fun w : NumberField.InfinitePlace L =>
      w.comap (algebraMap K L) = v)).card =
    Multiset.card (normalizedFactors
      (Polynomial.map
        ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom.comp
          (algebraMap K v.Completion))
        (minpoly K α))) := by
  have h := Fintype.card_congr (factors_equiv_places_above_real K L v hv α hα
    (theorem_13_5_tensor_product_iso v))
  simp only [Fintype.card_fin] at h
  rw [← Fintype.card_subtype]
  exact h.symm

theorem corollary_13_6_places_above_complex
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex)
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤) :
    (Finset.univ.filter (fun w : NumberField.InfinitePlace L =>
      w.comap (algebraMap K L) = v)).card =
    finrank K L := by
  have h := Fintype.card_congr (deg_equiv_places_above_complex K L v hv α hα
    (theorem_13_5_tensor_product_iso v))
  simp only [Fintype.card_fin] at h
  rw [← Fintype.card_subtype]
  exact h.symm

theorem factors_equiv_places_above_finite
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hiso : Nonempty (TensorProduct K L (v.adicCompletion K) ≃ₐ[K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L))) :
    Nonempty (
      { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } ≃
      { q : (v.adicCompletion K)[X] //
        q.Monic ∧ Irreducible q ∧
        q ∣ Polynomial.map (algebraMap K (v.adicCompletion K)) (minpoly K α) }) := by sorry

theorem completion_ringEquiv_adjoinRoot
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤)
    (e : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } ≃
      { q : (v.adicCompletion K)[X] //
        q.Monic ∧ Irreducible q ∧
        q ∣ Polynomial.map (algebraMap K (v.adicCompletion K)) (minpoly K α) })
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    Nonempty (w.adicCompletion L ≃+* AdjoinRoot (e ⟨w, hw⟩).val) := by sorry

theorem corollary_13_6_places_above_finite
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤) :
    Nonempty (
      { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } ≃
      { q : (v.adicCompletion K)[X] //
        q.Monic ∧ Irreducible q ∧
        q ∣ Polynomial.map (algebraMap K (v.adicCompletion K)) (minpoly K α) }) :=
  factors_equiv_places_above_finite K L v α hα (theorem_13_5_finite_place v)

theorem corollary_13_6_completion_iso_finite
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) (hα : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    ∃ (q : (v.adicCompletion K)[X]),
      q.Monic ∧ Irreducible q ∧
      q ∣ Polynomial.map (algebraMap K (v.adicCompletion K)) (minpoly K α) ∧
      Nonempty (w.adicCompletion L ≃+* AdjoinRoot q) := by


  obtain ⟨e⟩ := corollary_13_6_places_above_finite K L v α hα


  exact ⟨(e ⟨w, hw⟩).val, (e ⟨w, hw⟩).prop.1, (e ⟨w, hw⟩).prop.2.1,
    (e ⟨w, hw⟩).prop.2.2, completion_ringEquiv_adjoinRoot K L v α hα e w hw⟩

end IrreducibleFactorsAndPlaces

section GaloisOrbitsAndPlaces

def corollary_13_7_orbit_equiv
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K] :
    Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (NumberField.InfinitePlace K)) ≃
      NumberField.InfinitePlace k :=
  InfinitePlace.orbitRelEquiv

theorem corollary_13_7_mem_orbit_iff
    {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {w w' : NumberField.InfinitePlace K} :
    w' ∈ MulAction.orbit (K ≃ₐ[k] K) w ↔
      w.comap (algebraMap k K) = w'.comap (algebraMap k K) :=
  InfinitePlace.mem_orbit_iff

theorem corollary_13_7_exists_smul_eq
    {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {w w' : NumberField.InfinitePlace K}
    (h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)) :
    ∃ σ : K ≃ₐ[k] K, σ • w = w' :=
  InfinitePlace.exists_smul_eq_of_comap_eq h

theorem corollary_13_7_comap_surjective
    (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective
      (InfinitePlace.comap · (algebraMap k K) : InfinitePlace K → InfinitePlace k) :=
  InfinitePlace.comap_surjective

theorem corollary_13_7_mk_eq_iff {K : Type*} [Field K] {φ ψ : K →+* ℂ} :
    InfinitePlace.mk φ = InfinitePlace.mk ψ ↔
      φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ :=
  InfinitePlace.mk_eq_iff

theorem place_isReal_or_isComplex {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) : w.IsReal ∨ w.IsComplex :=
  InfinitePlace.isReal_or_isComplex w

def ComplexEmbedding.conjugateSetoid (L : Type*) [Field L] :
    Setoid (L →+* ℂ) where
  r φ ψ := InfinitePlace.mk φ = InfinitePlace.mk ψ
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

theorem ComplexEmbedding.conjugateSetoid_rel_iff {L : Type*} [Field L]
    {φ ψ : L →+* ℂ} :
    (ComplexEmbedding.conjugateSetoid L).r φ ψ ↔
      (φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ) :=
  mk_eq_iff

def corollary_13_7_embedding_orbit_equiv_Q (L : Type*) [Field L] :
    Quotient (ComplexEmbedding.conjugateSetoid L) ≃
      NumberField.InfinitePlace L where
  toFun := Quotient.lift InfinitePlace.mk (fun _ _ h => h)
  invFun w := Quotient.mk (ComplexEmbedding.conjugateSetoid L) w.embedding
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun φ => by
      simp only [Quotient.lift_mk]
      exact Quotient.sound (mk_embedding (mk φ))
  right_inv := by
    intro w
    simp only [Quotient.lift_mk]
    exact w.mk_embedding

def EmbeddingsAbove (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) : Type _ :=
  { φ : L →+* ℂ // (InfinitePlace.mk φ).comap (algebraMap K L) = v }

def conjugateSetoidAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Setoid (EmbeddingsAbove K v (L := L)) where
  r φ ψ := InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def corollary_13_7_embeddings_equiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Quotient (conjugateSetoidAbove v (K := K) (L := L)) ≃
      { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } where
  toFun := Quotient.lift
    (fun (φ : EmbeddingsAbove K v) =>
      (⟨InfinitePlace.mk φ.val, by rw [comap_mk]; exact φ.prop⟩ :
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }))
    (fun φ ψ (h : InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val) => by
      simp only [Subtype.mk.injEq]
      exact h)
  invFun w := by
    refine Quotient.mk (conjugateSetoidAbove v) ⟨w.val.embedding, ?_⟩
    rw [comap_mk]
    rw [← comap_mk]
    rw [w.val.mk_embedding]
    exact w.prop
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun ⟨φ, hφ⟩ => by
      simp only [Quotient.lift_mk]
      apply Quotient.sound
      show InfinitePlace.mk (InfinitePlace.mk φ).embedding = InfinitePlace.mk φ
      exact (InfinitePlace.mk φ).mk_embedding
  right_inv := by
    intro ⟨w, hw⟩
    simp only [Quotient.lift_mk, Subtype.mk.injEq]
    exact w.mk_embedding

end GaloisOrbitsAndPlaces

section RealComplexEmbeddings

variable {K : Type*} [Field K]

abbrev IsRealEmbedding (φ : K →+* ℂ) : Prop := ComplexEmbedding.IsReal φ

abbrev IsComplexEmbedding (φ : K →+* ℂ) : Prop := ¬ ComplexEmbedding.IsReal φ

theorem isRealEmbedding_iff_isReal_place {φ : K →+* ℂ} :
    IsRealEmbedding φ ↔ (InfinitePlace.mk φ).IsReal := by
  constructor
  · intro h
    exact ⟨φ, h, rfl⟩
  · intro h
    exact InfinitePlace.isReal_of_mk_isReal h

theorem isComplexEmbedding_iff_isComplex_place {φ : K →+* ℂ} :
    IsComplexEmbedding φ ↔ (InfinitePlace.mk φ).IsComplex := by
  rw [IsComplexEmbedding, ← InfinitePlace.not_isReal_iff_isComplex]
  exact not_congr isRealEmbedding_iff_isReal_place

end RealComplexEmbeddings

section DegreeFormula

theorem corollary_13_9 (K : Type*) [Field K] [NumberField K] :
    nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K :=
  card_add_two_mul_card_eq_rank K

open Classical in
theorem card_complex_embeddings_eq (K : Type*) [Field K] [NumberField K] :
    card { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPlaces K :=
  card_complex_embeddings K

open Classical in
theorem card_real_embeddings_eq (K : Type*) [Field K] [NumberField K] :
    card { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } = nrRealPlaces K :=
  card_real_embeddings K

end DegreeFormula

section DiscriminantSign

theorem proposition_13_11 (K : Type*) [Field K] [NumberField K] :
    (NumberField.discr K).sign = (-1) ^ nrComplexPlaces K :=
  NumberField.sign_discr K

theorem discr_ne_zero' (K : Type*) [Field K] [NumberField K] :
    NumberField.discr K ≠ 0 :=
  NumberField.discr_ne_zero K

end DiscriminantSign


alias tensorProductDecomp_denseRange := theorem_13_5_dense_embedding
alias tensorProductDecomp_infinitePlace := theorem_13_5_tensor_product_iso
alias tensorProductDecomp_infinitePlace_Kv := theorem_13_5_tensor_product_iso_Kv
alias tensorProductDecomp_finitePlace := theorem_13_5_finite_place
alias tensorProductDecomp_finitePlace_Kv := theorem_13_5_finite_place_Kv


alias infinitePlace_card_eq_real_add_complex := corollary_13_6_factor_count
alias irredFactors_card_eq_infinitePlace_card := corollary_13_6_irred_factors
alias placesAboveReal_card_eq_irredFactors := corollary_13_6_places_above_real
alias placesAboveComplex_card_eq_finrank := corollary_13_6_places_above_complex
alias placesAboveFinite_equiv_irredFactors := corollary_13_6_places_above_finite
alias completionIso_finitePlace_adjoinRoot := corollary_13_6_completion_iso_finite


alias galoisOrbit_infinitePlace_equiv := corollary_13_7_orbit_equiv
alias infinitePlace_mem_orbit_iff_comap_eq := corollary_13_7_mem_orbit_iff
alias infinitePlace_exists_smul_eq_of_comap_eq := corollary_13_7_exists_smul_eq
alias infinitePlace_comap_surjective := corollary_13_7_comap_surjective
alias infinitePlace_mk_eq_iff_conjugate := corollary_13_7_mk_eq_iff
alias conjugateOrbit_equiv_infinitePlace := corollary_13_7_embedding_orbit_equiv_Q
alias conjugateOrbitAbove_equiv_placesAbove := corollary_13_7_embeddings_equiv


alias nrRealPlaces_add_two_nrComplexPlaces_eq_finrank := corollary_13_9


alias discr_sign_eq_neg_one_pow_nrComplexPlaces := proposition_13_11


alias tensorProduct_isSemisimpleRing_finitePlace := prop_4_36_tensorProduct_finite_isSemisimpleRing
alias completionEmbedding_finiteDimensional := prop_10_3_10_4_finiteDimensional_completion
alias finrank_tensorProduct_eq_finrank_completionProd := prop_10_3_10_4_finrank_eq
alias localDegree_eq_ramificationIdx_mul_inertiaDeg := thm_11_23_4_local_degree_ef
alias finrank_eq_sum_localDegrees := thm_5_35_11_23_degree_identity_finrank
alias canonicalMap_finite_ker_no_nonzero_idempotent := cor_4_32_no_nonzero_idempotent_in_ker_finite
alias completionProd_finiteDimensional_infinitePlace := canonicalMap_surjective_hfd_tgt
alias finrank_tensorProduct_eq_finrank_completionProd_infinite := canonicalMap_surjective_hdim
alias finrank_eq_sum_localDegrees_infinite := degree_identity_infinite_finrank
alias canonicalMap_finite_completionLinear := canonicalMap_finite_isKvLinear

end
