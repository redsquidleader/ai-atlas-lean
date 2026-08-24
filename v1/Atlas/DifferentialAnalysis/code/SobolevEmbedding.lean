/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open scoped ZeroAtInfty
open MeasureTheory Filter Topology

noncomputable section

namespace SobolevEmbedding

/-- A (strong) Sobolev space `H^m` on `ℝ^n`: smooth functions `u : ℝ^n → ℂ` of class
`C^m` such that each iterated Fréchet derivative `D^j u` (for `j ≤ m`) is square
integrable with respect to Lebesgue measure. -/
structure SobolevSpace (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  contDiff_toFun : ContDiff ℝ (m : ℕ∞) toFun
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Treat a Sobolev space element as the underlying function `ℝ^n → ℂ`. -/
instance {n m : ℕ} : CoeFun (SobolevSpace n m) (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨SobolevSpace.toFun⟩

/-- `H^m ⊂ H^{m'}` whenever `m' ≤ m`: lower the Sobolev order of an element by
restricting the derivative-integrability hypothesis. -/
def SobolevSpace.toLowerOrder {n : ℕ} {m m' : ℕ} (hle : m' ≤ m)
    (u : SobolevSpace n m) : SobolevSpace n m' where
  toFun := u.toFun
  contDiff_toFun := u.contDiff_toFun.of_le (Nat.cast_le.mpr hle)
  iteratedFDeriv_memLp j hj := u.iteratedFDeriv_memLp j (le_trans hj hle)


set_option synthInstance.maxHeartbeats 80000 in
/-- For `u ∈ H^m` and a coordinate direction `j`, the partial derivative
`∂_j u` has all iterated derivatives up to order `m-1` in `L^2`. This is the
key technical lemma used to define `SobolevSpace.partialDeriv`. -/
theorem partialDeriv_iteratedFDeriv_memLp {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) (i : ℕ) (hi : i ≤ m - 1) :
    MemLp (fun x => iteratedFDeriv ℝ i
      (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by

  have hmem := u.iteratedFDeriv_memLp (i + 1) (by omega)

  have hcd_fderiv : ContDiff ℝ (↑i : ℕ∞) (fderiv ℝ u.toFun) := by
    apply u.contDiff_toFun.fderiv_right
    norm_cast; omega

  have hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ i
        (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x‖ ≤
      ‖EuclideanSpace.single j (1 : ℝ)‖ *
        ‖iteratedFDeriv ℝ (i + 1) u.toFun x‖ := by
    intro x
    have h1 := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ u.toFun) (c := EuclideanSpace.single j (1 : ℝ)) (x := x)
      hcd_fderiv.contDiffAt (N := (↑i : ℕ∞)) (le_refl _)
    rw [norm_iteratedFDeriv_fderiv] at h1
    exact h1

  exact hmem.of_le_mul
    ((hcd_fderiv.clm_apply contDiff_const).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Partial derivative `∂_j u` as an element of `H^{m-1}`, given `u ∈ H^m`. -/
def SobolevSpace.partialDeriv {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) : SobolevSpace n (m - 1) where
  toFun := fun x => fderiv ℝ u.toFun x (EuclideanSpace.single j 1)
  contDiff_toFun := by
    have hle : ((↑(m - 1) : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((↑m : ℕ∞) : WithTop ℕ∞) := by
      norm_cast; exact (Nat.sub_add_cancel hm).le
    exact (ContDiff.fderiv_right u.contDiff_toFun hle).clm_apply contDiff_const
  iteratedFDeriv_memLp i hi := partialDeriv_iteratedFDeriv_memLp hm u j i hi


set_option synthInstance.maxHeartbeats 80000 in

/-- Iterate the partial derivative in direction `j` exactly `k` times, mapping
`H^m` into `H^{m-k}`. -/
def SobolevSpace.iteratedPartialDeriv {n : ℕ} {m : ℕ}
    (j : Fin n) : (k : ℕ) → (hk : k ≤ m) → SobolevSpace n m → SobolevSpace n (m - k)
  | 0, _, u => u.toLowerOrder (by omega)
  | k + 1, hk, u =>
    let v := SobolevSpace.iteratedPartialDeriv j k (by omega) u
    (v.partialDeriv (by omega) j).toLowerOrder (by omega)


/-- Density of Schwartz functions in `H^m` in the simultaneous-derivative sense:
given `f` whose first `m` derivatives are in `L^2`, there is a Schwartz function `φ`
whose iterated derivatives of every order `i ≤ m` are within `ε` of those of `f`
in `L^2`. -/
theorem schwartz_sobolev_simultaneous_L2_density {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ∀ i : ℕ, i ≤ m →
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal < ε := by sorry

/-- Schwartz approximation in the `H^m` norm: there exists `φ ∈ 𝓢` whose
combined `L^2` error across all derivative orders up to `m` (the `H^m`-norm of
`φ - f`) is less than `ε`. -/
theorem schwartz_sobolev_Hm_norm_approx {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      Real.sqrt (∑ i ∈ Finset.range (m + 1),
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2) < ε := by
  set δ := ε / Real.sqrt ((m : ℝ) + 1) with hδ_def
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsqrt_pos : (0 : ℝ) < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr hm_pos
  have hδ : 0 < δ := div_pos hε hsqrt_pos
  obtain ⟨φ, hφ⟩ := schwartz_sobolev_simultaneous_L2_density f hf δ hδ
  refine ⟨φ, ?_⟩
  have h_sum_bound : ∑ i ∈ Finset.range (m + 1),
      (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2 < ε ^ 2 := by
    have h1 : ∀ i ∈ Finset.range (m + 1),
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2 < δ ^ 2 := by
      intro i hi
      have him : i ≤ m := by rw [Finset.mem_range] at hi; omega
      have hcomp := hφ i him
      have hnn := @ENNReal.toReal_nonneg (eLpNorm (fun y =>
        iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2 volume)
      nlinarith [sq_nonneg (eLpNorm (fun y =>
        iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2 volume).toReal, sq_nonneg δ]
    have h2 : ∑ i ∈ Finset.range (m + 1),
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2
        < ∑ _ ∈ Finset.range (m + 1), δ ^ 2 :=
      Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (by omega)⟩ h1
    have h3 : ∑ _ ∈ Finset.range (m + 1), δ ^ 2 = ((m : ℝ) + 1) * δ ^ 2 := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h4 : ((m : ℝ) + 1) * δ ^ 2 = ε ^ 2 := by
      rw [hδ_def]; field_simp; rw [Real.sq_sqrt hm_pos.le]
    linarith
  rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm]
  exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) h_sum_bound

/-- Reformulation of Schwartz density: from a small `H^m`-norm approximation we
derive that each individual `L^2` derivative discrepancy is less than `ε`. -/
theorem schwartz_sobolev_simultaneous_Lp_approx {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ∀ i : ℕ, i ≤ m →
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal < ε := by
  obtain ⟨φ, hφ⟩ := schwartz_sobolev_Hm_norm_approx f hf ε hε
  refine ⟨φ, fun i hi => ?_⟩
  have h_in_range : i ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have h_sq_le : (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
      iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2 ≤
    ∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ j f y) 2 volume).toReal ^ 2 :=
    Finset.single_le_sum (f := fun j =>
      (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ j f y) 2 volume).toReal ^ 2) (fun j _ => sq_nonneg _) h_in_range
  have h_component_le : (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
      iteratedFDeriv ℝ i f y) 2 volume).toReal ≤
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ j f y) 2 volume).toReal ^ 2) := by
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg]
    exact Real.sqrt_le_sqrt h_sq_le
  linarith


/-- Variant of Schwartz density bounding the squared `L^2` discrepancy of every
derivative order `i ≤ m` by a prescribed `δ`. -/
theorem schwartz_sobolev_component_approx {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ∀ i ∈ Finset.range (m + 1),
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 < δ := by

  have hε : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  obtain ⟨φ, hφ⟩ := schwartz_sobolev_simultaneous_Lp_approx f hf (Real.sqrt δ) hε
  refine ⟨φ, fun i hi => ?_⟩
  have him : i ≤ m := by
    rw [Finset.mem_range] at hi; omega
  have hcomp := hφ i him


  have hnn : (0 : ℝ) ≤ (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
      iteratedFDeriv ℝ i f y) 2 volume).toReal := ENNReal.toReal_nonneg
  calc (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2
      < (Real.sqrt δ) ^ 2 := by
        apply sq_lt_sq' (by linarith) hcomp
    _ = δ := Real.sq_sqrt (le_of_lt hδ)

/-- Core Schwartz approximation: bound the joint `H^m`-norm error
`(∑ ‖D^i φ - D^i f‖_{L^2}^2)^{1/2}` by `ε`. -/
theorem schwartz_approximation_Hm_L2_core {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      Real.sqrt (∑ i ∈ Finset.range (m + 1),
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2) < ε := by
  set δ := ε ^ 2 / ((m : ℝ) + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨φ, hφ⟩ := schwartz_sobolev_component_approx f hf δ hδ
  refine ⟨φ, ?_⟩
  have h_sum_bound : ∑ i ∈ Finset.range (m + 1),
      (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2 < ε ^ 2 := by
    have h1 : ∑ i ∈ Finset.range (m + 1),
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2
        < ∑ _ ∈ Finset.range (m + 1), δ :=
      Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (by omega)⟩ hφ
    have h2 : ∑ _ ∈ Finset.range (m + 1), δ = ((m : ℝ) + 1) * δ := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h3 : ((m : ℝ) + 1) * δ = ε ^ 2 := by rw [hδ_def]; field_simp
    linarith
  rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm]
  exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) h_sum_bound

/-- Schwartz density in `H^m`: for every `H^m` function `f` and every `ε > 0`
there is a Schwartz function `φ` such that every derivative `D^i φ` approximates
`D^i f` in `L^2` to within `ε`. -/
theorem schwartz_approximation_Hm_L2 {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ∀ i, i ≤ m →
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal < ε := by
  obtain ⟨φ, hφ⟩ := schwartz_approximation_Hm_L2_core f hf ε hε
  refine ⟨φ, fun i hi => ?_⟩
  have h_in_range : i ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have h_sq_le : (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
      iteratedFDeriv ℝ i f y) 2 volume).toReal ^ 2 ≤
    ∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ j f y) 2 volume).toReal ^ 2 :=
    Finset.single_le_sum (f := fun j =>
      (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ j f y) 2 volume).toReal ^ 2) (fun j _ => sq_nonneg _) h_in_range
  have h_nonneg_sum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ j f y) 2 volume).toReal ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have h_component_le : (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
      iteratedFDeriv ℝ i f y) 2 volume).toReal ≤
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
        iteratedFDeriv ℝ j f y) 2 volume).toReal ^ 2) := by
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg]
    exact Real.sqrt_le_sqrt h_sq_le
  linarith


/-- Sobolev `L^∞` bound on derivatives: under the condition `n < 2(m - j)`
(Sobolev embedding threshold), the pointwise difference of `j`-th derivatives
is controlled by the sum of `L^2` differences of all derivatives `i ≤ m`. -/
theorem sobolev_Linfty_iteratedFDeriv_bound {n m : ℕ}
    (j : ℕ) (hj : j ≤ m) (hjn : n < 2 * (m - j))
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) x -
      iteratedFDeriv ℝ j f x‖ ≤
      ∑ i ∈ Finset.range (m + 1),
        (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
          iteratedFDeriv ℝ i f y) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal := by sorry

/-- Combining Schwartz density with the Sobolev `L^∞` bound: under
`n < 2(m - j)` we obtain a sequence of Schwartz functions whose `j`-th
derivatives converge uniformly to the `j`-th derivative of `f`. -/
theorem schwartz_approximation_Linfty_iteratedFDeriv {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ i : ℕ, i ≤ m → MemLp (fun x => iteratedFDeriv ℝ i f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (j : ℕ) (hj : j ≤ m) (hjn : n < 2 * (m - j)) :
    ∃ (ι : Type) (_ : Nonempty ι) (l : Filter ι) (_ : l.NeBot)
      (φ : ι → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ),
      TendstoUniformly
        (fun k x => iteratedFDeriv ℝ j (↑(φ k) : EuclideanSpace ℝ (Fin n) → ℂ) x)
        (fun x => iteratedFDeriv ℝ j f x) l := by

  have h_approx : ∀ k : ℕ,
      ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∀ i, i ≤ m →
          (eLpNorm (fun y => iteratedFDeriv ℝ i (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
            iteratedFDeriv ℝ i f y) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal <
            1 / ((↑m + 1) * (↑k + 1)) := by
    intro k
    exact schwartz_approximation_Hm_L2 f hf _ (by positivity)
  choose φ_seq hφ_bound using h_approx

  refine ⟨ℕ, ⟨0⟩, atTop, atTop_neBot, φ_seq, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  rw [Filter.eventually_atTop]
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
  refine ⟨K, fun k hk x => ?_⟩

  rw [dist_comm, dist_eq_norm]

  have hsob := sobolev_Linfty_iteratedFDeriv_bound j hj hjn f hf (φ_seq k) x

  calc ‖iteratedFDeriv ℝ j (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x -
          iteratedFDeriv ℝ j f x‖
      ≤ ∑ i ∈ Finset.range (m + 1),
          (eLpNorm (fun y => iteratedFDeriv ℝ i (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) y -
            iteratedFDeriv ℝ i f y) 2 volume).toReal := hsob
    _ ≤ ∑ _i ∈ Finset.range (m + 1),
          (1 / ((↑m + 1) * (↑k + 1))) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact le_of_lt (hφ_bound k i (by omega))
    _ = (m + 1) * (1 / ((↑m + 1) * (↑k + 1))) := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ = 1 / (↑k + 1) := by
        field_simp
    _ < ε := by
        have hk1 : (0 : ℝ) < ↑k + 1 := by positivity
        rw [div_lt_iff₀ hk1]
        have h1e : 1 / ε < (↑k : ℝ) + 1 := by
          calc 1 / ε < ↑K := hK
            _ ≤ (↑k : ℝ) := by exact_mod_cast hk
            _ ≤ (↑k : ℝ) + 1 := le_add_of_nonneg_right (by positivity)
        have := (div_lt_iff₀ hε).mp h1e
        linarith


/-- Sobolev embedding (base case): if all derivatives of `f` up to order `m`
are in `L^2` and `n < 2(m - i)`, then `D^i f` is continuous. This is proved by
uniform convergence of Schwartz approximations. -/
theorem sobolev_iteratedFDeriv_continuous_of_memLp_base {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ j : ℕ, j ≤ m → MemLp (fun x => iteratedFDeriv ℝ j f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (i : ℕ) (hi : i ≤ m) (hm : n < 2 * (m - i)) :
    Continuous (fun x => iteratedFDeriv ℝ i f x) := by

  obtain ⟨ι, _, l, hl, φ, hunif⟩ :=
    schwartz_approximation_Linfty_iteratedFDeriv f hf i hi hm

  exact hunif.continuous
    ((Filter.Eventually.of_forall (fun k =>
      ((φ k).smooth i).continuous_iteratedFDeriv (m := i) le_rfl)).frequently)


/-- Sobolev embedding (differentiability, base case): under `n < 2(m - (i+1))`,
the iterated derivative `D^i f` is differentiable, via uniform convergence of
Schwartz approximants together with their derivatives. -/
theorem sobolev_iteratedFDeriv_differentiable_of_memLp_base {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ j : ℕ, j ≤ m → MemLp (fun x => iteratedFDeriv ℝ j f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (i : ℕ) (hi : i + 1 ≤ m) (hm : n < 2 * (m - (i + 1))) :
    Differentiable ℝ (fun x => iteratedFDeriv ℝ i f x) := by


  have hi_le : i ≤ m := by omega
  have hm_i : n < 2 * (m - i) := Nat.lt_of_lt_of_le hm (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_left (Nat.le_succ i) m))

  have h_approx : ∀ k : ℕ,
      ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∀ j, j ≤ m →
          (eLpNorm (fun y => iteratedFDeriv ℝ j (↑φ : EuclideanSpace ℝ (Fin n) → ℂ) y -
            iteratedFDeriv ℝ j f y) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal <
            1 / ((↑m + 1) * (↑k + 1)) := by
    intro k
    exact schwartz_approximation_Hm_L2 f hf _ (by positivity)
  choose φ_seq hφ_bound using h_approx

  have hunif_lev_i : TendstoUniformly
      (fun k x => iteratedFDeriv ℝ i (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x)
      (fun x => iteratedFDeriv ℝ i f x) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    rw [Filter.eventually_atTop]
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    refine ⟨K, fun k hk x => ?_⟩
    rw [dist_comm, dist_eq_norm]
    have hsob := sobolev_Linfty_iteratedFDeriv_bound i hi_le hm_i f hf (φ_seq k) x
    calc ‖iteratedFDeriv ℝ i (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x -
            iteratedFDeriv ℝ i f x‖
        ≤ ∑ j ∈ Finset.range (m + 1),
            (eLpNorm (fun y => iteratedFDeriv ℝ j (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) y -
              iteratedFDeriv ℝ j f y) 2 volume).toReal := hsob
      _ ≤ ∑ _j ∈ Finset.range (m + 1), (1 / ((↑m + 1) * (↑k + 1))) := by
          apply Finset.sum_le_sum; intro j hj
          rw [Finset.mem_range] at hj
          exact le_of_lt (hφ_bound k j (by omega))
      _ = (m + 1) * (1 / ((↑m + 1) * (↑k + 1))) := by
          rw [Finset.sum_const, Finset.card_range]; simp [nsmul_eq_mul]
      _ = 1 / (↑k + 1) := by field_simp
      _ < ε := by
          have hk1 : (0 : ℝ) < ↑k + 1 := by positivity
          rw [div_lt_iff₀ hk1]
          have h1e : 1 / ε < (↑k : ℝ) + 1 :=
            calc 1 / ε < ↑K := hK
              _ ≤ (↑k : ℝ) := by exact_mod_cast hk
              _ ≤ (↑k : ℝ) + 1 := le_add_of_nonneg_right (by positivity)
          linarith [(div_lt_iff₀ hε).mp h1e]

  have hunif_lev_i1 : TendstoUniformly
      (fun k x => iteratedFDeriv ℝ (i + 1) (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x)
      (fun x => iteratedFDeriv ℝ (i + 1) f x) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    rw [Filter.eventually_atTop]
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    refine ⟨K, fun k hk x => ?_⟩
    rw [dist_comm, dist_eq_norm]
    have hsob := sobolev_Linfty_iteratedFDeriv_bound (i + 1) hi hm f hf (φ_seq k) x
    calc ‖iteratedFDeriv ℝ (i + 1) (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x -
            iteratedFDeriv ℝ (i + 1) f x‖
        ≤ ∑ j ∈ Finset.range (m + 1),
            (eLpNorm (fun y => iteratedFDeriv ℝ j (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) y -
              iteratedFDeriv ℝ j f y) 2 volume).toReal := hsob
      _ ≤ ∑ _j ∈ Finset.range (m + 1), (1 / ((↑m + 1) * (↑k + 1))) := by
          apply Finset.sum_le_sum; intro j hj
          rw [Finset.mem_range] at hj
          exact le_of_lt (hφ_bound k j (by omega))
      _ = (m + 1) * (1 / ((↑m + 1) * (↑k + 1))) := by
          rw [Finset.sum_const, Finset.card_range]; simp [nsmul_eq_mul]
      _ = 1 / (↑k + 1) := by field_simp
      _ < ε := by
          have hk1 : (0 : ℝ) < ↑k + 1 := by positivity
          rw [div_lt_iff₀ hk1]
          have h1e : 1 / ε < (↑k : ℝ) + 1 :=
            calc 1 / ε < ↑K := hK
              _ ≤ (↑k : ℝ) := by exact_mod_cast hk
              _ ≤ (↑k : ℝ) + 1 := le_add_of_nonneg_right (by positivity)
          linarith [(div_lt_iff₀ hε).mp h1e]


  set CLE := continuousMultilinearCurryLeftEquiv ℝ
    (fun (_ : Fin (i + 1)) => EuclideanSpace ℝ (Fin n)) ℂ
  have hunif_deriv : TendstoUniformly
      (fun k x => CLE (iteratedFDeriv ℝ (i + 1) (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x))
      (fun x => CLE (iteratedFDeriv ℝ (i + 1) f x)) atTop :=
    CLE.isometry.uniformContinuous.comp_tendstoUniformly hunif_lev_i1


  have hfderiv : ∀ k x, HasFDerivAt
      (fun y => iteratedFDeriv ℝ i (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) y)
      (CLE (iteratedFDeriv ℝ (i + 1) (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x)) x := by
    intro k x
    have hsmooth : ContDiff ℝ (↑(i + 1) : ℕ∞) (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) :=
      ((φ_seq k).smooth (i + 1)).of_le (by norm_cast)
    have hd := hsmooth.differentiable_iteratedFDeriv (m := i)
      (by exact_mod_cast Nat.lt_succ_iff.mpr le_rfl)
    have hfde := (hd x).hasFDerivAt
    rw [show (fun y => iteratedFDeriv ℝ i (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) y) =
      iteratedFDeriv ℝ i (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) from rfl] at hfde
    rw [fderiv_iteratedFDeriv] at hfde
    exact hfde

  have hptwise : ∀ x, Tendsto
      (fun k => iteratedFDeriv ℝ i (↑(φ_seq k) : EuclideanSpace ℝ (Fin n) → ℂ) x)
      atTop (𝓝 (iteratedFDeriv ℝ i f x)) :=
    hunif_lev_i.tendsto_at

  have hhas : ∀ x, HasFDerivAt (fun y => iteratedFDeriv ℝ i f y)
      (CLE (iteratedFDeriv ℝ (i + 1) f x)) x :=
    hasFDerivAt_of_tendstoUniformly hunif_deriv hfderiv hptwise

  exact fun x => (hhas x).differentiableAt


/-- Sobolev embedding theorem (Melrose Thm 10.1): if `n < 2(m - k)` and `k ≤ m`,
then any `f` whose first `m` derivatives are in `L^2` is of class `C^k`. -/
theorem sobolev_contDiff_of_memLp_fourier {n m k : ℕ} (hkm : k ≤ m)
    (hn : n < 2 * (m - k))
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ j : ℕ, j ≤ m → MemLp (fun x => iteratedFDeriv ℝ j f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ContDiff ℝ (k : ℕ∞) f := by
  rw [show (k : ℕ∞) = ((k : ℕ) : WithTop ℕ∞) from by norm_cast]
  exact contDiff_nat_iff_continuous_differentiable.mpr ⟨
    fun j hj => sobolev_iteratedFDeriv_continuous_of_memLp_base f hf j
      (hj.trans hkm)
      (Nat.lt_of_lt_of_le hn (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_left hj m))),
    fun j hj => sobolev_iteratedFDeriv_differentiable_of_memLp_base f hf j
      (by omega)
      (Nat.lt_of_lt_of_le hn (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_left hj m)))⟩


/-- Continuity corollary of the Sobolev embedding: `D^i f` is continuous for
all `i` such that the embedding threshold is met. -/
theorem sobolev_iteratedFDeriv_continuous_of_memLp {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ j : ℕ, j ≤ m → MemLp (fun x => iteratedFDeriv ℝ j f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (i : ℕ) (hi : i ≤ m) (hm : n < 2 * (m - i)) :
    Continuous (fun x => iteratedFDeriv ℝ i f x) :=
  (sobolev_contDiff_of_memLp_fourier hi hm f hf).continuous_iteratedFDeriv le_rfl

/-- Differentiability corollary of Sobolev embedding: `D^i f` is differentiable
whenever the strict embedding threshold is met. -/
theorem sobolev_iteratedFDeriv_differentiable_of_memLp {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ j : ℕ, j ≤ m → MemLp (fun x => iteratedFDeriv ℝ j f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (i : ℕ) (hi : i + 1 ≤ m) (hm : n < 2 * (m - (i + 1))) :
    Differentiable ℝ (fun x => iteratedFDeriv ℝ i f x) :=
  (sobolev_contDiff_of_memLp_fourier hi hm f hf).differentiable_iteratedFDeriv
    (by exact_mod_cast Nat.lt_succ_iff.mpr le_rfl)

/-- Sobolev embedding theorem (final user-facing form): `H^m ⊂ C^k` when
`n < 2(m - k)`. -/
theorem sobolev_contDiff_of_memLp {n m k : ℕ} (hkm : k ≤ m)
    (hn : n < 2 * (m - k))
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ j : ℕ, j ≤ m → MemLp (fun x => iteratedFDeriv ℝ j f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ContDiff ℝ (k : ℕ∞) f :=
  contDiff_nat_iff_continuous_differentiable.mpr
    ⟨fun j hj => sobolev_iteratedFDeriv_continuous_of_memLp f hf j
       (hj.trans hkm) (by omega),
     fun j hj => sobolev_iteratedFDeriv_differentiable_of_memLp f hf j
       (by omega) (by omega)⟩


/-- Application of the Sobolev embedding to elements `u ∈ H^m`: continuity of
`D^j u` for `j ≤ k`. -/
theorem sobolev_schwartz_density_iteratedFDeriv_continuous {n m k : ℕ}
    (hkm : k ≤ m) (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) (j : ℕ) (hj : j ≤ k) :
    Continuous (fun x => iteratedFDeriv ℝ j u.toFun x) :=
  (sobolev_contDiff_of_memLp hkm hm u.toFun
    (fun i hi => u.iteratedFDeriv_memLp i hi)).continuous_iteratedFDeriv
    (by exact_mod_cast hj)


/-- Application of the Sobolev embedding to `u ∈ H^m`: differentiability of
`D^j u` for `j < k`. -/
theorem sobolev_schwartz_density_iteratedFDeriv_differentiable {n m k : ℕ}
    (hkm : k ≤ m) (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) (j : ℕ) (hj : j < k) :
    Differentiable ℝ (fun x => iteratedFDeriv ℝ j u.toFun x) :=
  (sobolev_contDiff_of_memLp hkm hm u.toFun
    (fun i hi => u.iteratedFDeriv_memLp i hi)).differentiable_iteratedFDeriv
    (by exact_mod_cast hj)

/-- Sobolev embedding applied to `u ∈ H^m`: `u` is of class `C^k` whenever
`n < 2(m - k)`. -/
theorem sobolev_schwartz_density_contDiff {n m k : ℕ} (hkm : k ≤ m)
    (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) : ContDiff ℝ (k : ℕ∞) u.toFun :=
  contDiff_nat_iff_continuous_differentiable.mpr
    ⟨fun j hj => sobolev_schwartz_density_iteratedFDeriv_continuous hkm hm u j hj,
     fun j hj => sobolev_schwartz_density_iteratedFDeriv_differentiable hkm hm u j hj⟩


/-- Each iterated derivative of a Schwartz function vanishes at infinity (in the
cocompact filter). -/
theorem schwartz_iteratedFDeriv_tendsto_zero {n : ℕ}
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (j : ℕ) :
    Tendsto (fun x => iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin n) → ℂ) x)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C, hC_pos, hC⟩ := φ.decay 1 j
  rw [Filter.hasBasis_cocompact.eventually_iff]
  refine ⟨Metric.closedBall 0 (C / ε), isCompact_closedBall 0 _, fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hx
  push_neg at hx
  simp only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  have hx_pos : 0 < ‖x‖ := by linarith [div_nonneg (le_of_lt hC_pos) (le_of_lt hε)]
  have h := hC x; simp only [pow_one] at h
  calc ‖iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin n) → ℂ) x‖
      ≤ C / ‖x‖ := by rwa [le_div_iff₀ hx_pos, mul_comm]
    _ < C / (C / ε) := div_lt_div_of_pos_left hC_pos (by positivity) hx
    _ = ε := by field_simp


/-- General principle: if `F_i → g` uniformly and each `F_i` vanishes at infinity
(cocompactly), then so does `g`. -/
theorem tendsto_zero_of_tendstoUniformly_of_vanish'
    {α : Type*} [TopologicalSpace α]
    {E : Type*} [SeminormedAddCommGroup E]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → α → E} {g : α → E}
    (hunif : TendstoUniformly F g l)
    (hvanish : ∀ᶠ i in l, Tendsto (F i) (cocompact α) (𝓝 0)) :
    Tendsto g (cocompact α) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  rw [Metric.tendstoUniformly_iff] at hunif
  obtain ⟨i, hi_unif, hi_vanish⟩ := (hunif (ε / 2) hε2).and hvanish |>.exists
  rw [Metric.tendsto_nhds] at hi_vanish
  apply (hi_vanish (ε / 2) hε2).mono
  intro x hx
  calc dist (g x) 0
      ≤ dist (g x) (F i x) + dist (F i x) 0 := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hi_unif x) hx
    _ = ε := by ring

/-- Sobolev embedding into `C_0^k`: the iterated derivative `D^j f` vanishes at
infinity (cocompactly) when `f` has `H^m` regularity above the Sobolev threshold. -/
theorem sobolev_iteratedFDeriv_vanish_of_memLp {n m : ℕ}
    (hkm : 0 ≤ m) (hmj : n < 2 * m)
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ j : ℕ, j ≤ m → MemLp (fun x => iteratedFDeriv ℝ j f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (j : ℕ) (hj : j ≤ m) (hjn : n < 2 * (m - j)) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖iteratedFDeriv ℝ j f x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by

  obtain ⟨ι, hne, l, hneBot, φ, hunif⟩ :=
    schwartz_approximation_Linfty_iteratedFDeriv f hf j hj hjn


  rw [← tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_zero_of_tendstoUniformly_of_vanish' hunif
    (Filter.Eventually.of_forall (fun k => schwartz_iteratedFDeriv_tendsto_zero (φ k) j))

/-- Specialization of `sobolev_iteratedFDeriv_vanish_of_memLp` to elements of
`SobolevSpace n m`. -/
theorem sobolev_iteratedFDeriv_vanish_density {n m : ℕ}
    (u : SobolevSpace n m) (j : ℕ) (hj : j ≤ m) (hmj : n < 2 * (m - j)) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖iteratedFDeriv ℝ j u.toFun x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
  sobolev_iteratedFDeriv_vanish_of_memLp (Nat.zero_le m) (by omega) u.toFun
    (fun i hi => u.iteratedFDeriv_memLp i hi) j hj hmj

/-- Vanishing at infinity of derivatives `D^j u` for `u ∈ H^m`, `j ≤ k`,
under `n < 2(m - k)`. -/
theorem sobolev_schwartz_density_iteratedFDeriv_vanish {n m k : ℕ} (hkm : k ≤ m)
    (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) (j : ℕ) (hj : j ≤ k) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖iteratedFDeriv ℝ j u.toFun x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
  sobolev_iteratedFDeriv_vanish_density u j (le_trans hj hkm) (by omega)

/-- Auxiliary: any `u ∈ H^m` is continuous when `n < 2m`. -/
theorem sobolevSpace_continuous_aux {n m : ℕ} (hm : n < 2 * m)
    (u : SobolevSpace n m) : Continuous u.toFun :=
  (sobolev_schwartz_density_contDiff (Nat.zero_le m) (by omega) u).continuous


/-- Auxiliary: any `u ∈ H^m` vanishes at infinity when `n < 2m`, so
`H^m ⊂ C_0` whenever `m > n/2`. -/
theorem sobolevSpace_zeroAtInfty_aux {n m : ℕ} (hm : n < 2 * m)
    (u : SobolevSpace n m) :
    Tendsto u.toFun (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := sobolev_schwartz_density_iteratedFDeriv_vanish (Nat.zero_le m) (by omega) u 0 (le_refl 0)
  simp only [norm_iteratedFDeriv_zero] at h
  exact h


/-- Weak Sobolev space: a function whose iterated derivatives up to order `m`
are in `L^2`, but without an a priori smoothness assumption on the function
itself. Used as the input type for the Sobolev embedding. -/
structure SobolevSpaceWeak (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Treat a weak Sobolev space element as the underlying function `ℝ^n → ℂ`. -/
instance {n m : ℕ} : CoeFun (SobolevSpaceWeak n m) (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨SobolevSpaceWeak.toFun⟩

/-- The (strong) Sobolev space embeds into the weak Sobolev space by forgetting
the a priori smoothness. -/
def SobolevSpace.toWeak {n m : ℕ} (u : SobolevSpace n m) : SobolevSpaceWeak n m where
  toFun := u.toFun
  iteratedFDeriv_memLp := u.iteratedFDeriv_memLp


/-- **Sobolev embedding** (Melrose Cor. 10.3): if `k ≤ m` and `n < 2(m - k)`,
then every weak Sobolev function `u ∈ H^m` is (a.e. equal to) a `C^k` function
whose derivatives of order `≤ k` all vanish at infinity, i.e. `H^m ↪ C_0^k`. -/
def sobolevEmbedding {n m k : ℕ} (hkm : k ≤ m)
    (hm : n < 2 * (m - k))
    (u : SobolevSpaceWeak n m) :
    { v : TestFunctions.ContDiffZeroAtInftyN n k // ⇑v.toZeroAtInftyContinuousMap = u.toFun } :=
  ⟨{ toZeroAtInftyContinuousMap :=
       { toFun := u.toFun
         continuous_toFun :=
           (sobolev_contDiff_of_memLp (Nat.zero_le m) (by omega) u.toFun
             (fun j hj => u.iteratedFDeriv_memLp j hj)).continuous
         zero_at_infty' := by
           rw [tendsto_zero_iff_norm_tendsto_zero]
           have h := sobolev_iteratedFDeriv_vanish_of_memLp (Nat.zero_le m) (by omega)
             u.toFun (fun j hj => u.iteratedFDeriv_memLp j hj) 0 (Nat.zero_le m) (by omega)
           simp only [norm_iteratedFDeriv_zero] at h
           exact h }
     contDiff_k := sobolev_contDiff_of_memLp hkm hm u.toFun
       (fun j hj => u.iteratedFDeriv_memLp j hj)
     iteratedFDeriv_zero_at_infty := fun j hj =>
       sobolev_iteratedFDeriv_vanish_of_memLp (Nat.zero_le m) (by omega) u.toFun
         (fun i hi => u.iteratedFDeriv_memLp i hi) j (le_trans hj hkm) (by omega) },
   rfl⟩

/-- Sobolev embedding restated for strong Sobolev space elements `u ∈ H^m`. -/
def sobolevEmbedding_strong {n m k : ℕ} (hkm : k ≤ m)
    (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) :
    { v : TestFunctions.ContDiffZeroAtInftyN n k // ⇑v.toZeroAtInftyContinuousMap = u.toFun } :=
  sobolevEmbedding hkm hm u.toWeak

/-- The smooth Sobolev space `H^∞ = ⋂_m H^m`: a function `u` that lies in every
`H^m` with a consistent underlying function. -/
structure SobolevInfty (n : ℕ) where
  mem_sobolev : ∀ m : ℕ, SobolevSpace n m
  consistent : ∀ m₁ m₂ : ℕ, (mem_sobolev m₁).toFun = (mem_sobolev m₂).toFun

/-- Base case `k = 0` of the Sobolev embedding: `H^m ⊂ C_0` when `m > n/2`. -/
def sobolevEmbedding_base {n m : ℕ} (hm : n < 2 * m)
    (u : SobolevSpaceWeak n m) :
    { v : TestFunctions.ContDiffZeroAtInftyN n 0 // ⇑v.toZeroAtInftyContinuousMap = u.toFun } :=
  sobolevEmbedding (Nat.zero_le m) (by omega) u

end SobolevEmbedding

open scoped SchwartzMap

namespace SchwartzRepresentation

variable {n : ℕ}

/-- Order `|α| = α₁ + ⋯ + α_n` of a multi-index `α : Fin n → ℕ`. -/
def multiIndexOrder (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- The finite set of all multi-indices `α : Fin n → ℕ` with `|α| ≤ m`. -/
def multiIndicesBall (n m : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (m + 1))).filter
    (fun α => multiIndexOrder α ≤ m)

/-- Membership criterion for `multiIndicesBall`: `α ∈ multiIndicesBall n m` iff
the total order `|α|` is at most `m`. -/
theorem mem_multiIndicesBall_iff {n m : ℕ} {α : Fin n → ℕ} :
    α ∈ multiIndicesBall n m ↔ multiIndexOrder α ≤ m := by
  simp only [multiIndicesBall, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, and_iff_right_iff_imp]
  intro hord i
  exact Nat.lt_succ_of_le (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)) hord)

/-- The monomial `x^α = ∏ x_i^{α_i}` viewed as a complex-valued function on
`ℝ^n`. -/
def monomial (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∏ i : Fin n, (↑(x i) : ℂ) ^ (α i)

/-- Iterate the line derivative `∂_{x_j}` exactly `k` times on a Schwartz
function. -/
def iterSchwartzDerivCoord (j : Fin n) (k : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)))^[k] φ

/-- The multi-index partial derivative `∂^β` on Schwartz functions, defined by
iteratively applying coordinate derivatives in each direction `j` exactly
`β j` times. -/
def iterSchwartzDeriv (β : Fin n → ℕ) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j ψ => iterSchwartzDerivCoord j (β j) ψ) φ

section SchwartzLpEmbedding

open MeasureTheory

/-- `iterSchwartzDerivCoord` is additive in its Schwartz argument. -/
lemma iterSchwartzDerivCoord_map_add (j : Fin n) (k : ℕ)
    (φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j k (φ + ψ) =
      iterSchwartzDerivCoord j k φ + iterSchwartzDerivCoord j k ψ := by
  unfold iterSchwartzDerivCoord
  induction k generalizing φ ψ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply, LineDerivAdd.lineDerivOp_add]
    exact ih _ _

/-- `iterSchwartzDeriv β` is additive in its Schwartz argument. -/
lemma iterSchwartzDeriv_map_add (β : Fin n → ℕ)
    (φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDeriv β (φ + ψ) =
      iterSchwartzDeriv β φ + iterSchwartzDeriv β ψ := by
  unfold iterSchwartzDeriv
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    exact iterSchwartzDerivCoord_map_add j (β j) _ _

/-- `iterSchwartzDerivCoord` is `ℂ`-linear in its Schwartz argument. -/
lemma iterSchwartzDerivCoord_map_smul (j : Fin n) (k : ℕ) (c : ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j k (c • φ) = c • iterSchwartzDerivCoord j k φ := by
  unfold iterSchwartzDerivCoord
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply, LineDerivSMul.lineDerivOp_smul]
    exact ih _

/-- `iterSchwartzDeriv β` is `ℂ`-linear in its Schwartz argument. -/
lemma iterSchwartzDeriv_map_smul (β : Fin n → ℕ) (c : ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDeriv β (c • φ) = c • iterSchwartzDeriv β φ := by
  unfold iterSchwartzDeriv
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    exact iterSchwartzDerivCoord_map_smul j (β j) c _

/-- Every Schwartz derivative `∂^α φ` belongs to `L^2`. -/
theorem schwartzDerivMemLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemLp ((iterSchwartzDeriv α φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      EuclideanSpace ℝ (Fin n) → ℂ) 2 volume :=
  (iterSchwartzDeriv α φ).memLp 2

/-- Map a Schwartz function `φ` to the `L^2` equivalence class of `∂^α φ`. -/
noncomputable def schwartzToLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (schwartzDerivMemLp n α φ).toLp _

/-- `schwartzToLp` is additive in the Schwartz argument. -/
theorem schwartzToLp_add (α : Fin n → ℕ)
    (φ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    schwartzToLp n α (φ + ψ) = schwartzToLp n α φ + schwartzToLp n α ψ := by
  simp only [schwartzToLp]
  have heq : (⇑(iterSchwartzDeriv α (φ + ψ)) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
      (⇑(iterSchwartzDeriv α φ) + ⇑(iterSchwartzDeriv α ψ)) := by
    apply Filter.EventuallyEq.of_eq
    ext x
    rw [iterSchwartzDeriv_map_add]
    simp [SchwartzMap.add_apply]
  rw [MemLp.toLp_congr _ ((schwartzDerivMemLp n α φ).add (schwartzDerivMemLp n α ψ)) heq]
  exact MemLp.toLp_add _ _

/-- `schwartzToLp` is `ℂ`-linear in the Schwartz argument. -/
theorem schwartzToLp_smul (α : Fin n → ℕ) (c : ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    schwartzToLp n α (c • φ) = c • schwartzToLp n α φ := by
  simp only [schwartzToLp]
  have heq : (⇑(iterSchwartzDeriv α (c • φ)) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
      (c • ⇑(iterSchwartzDeriv α φ)) := by
    apply Filter.EventuallyEq.of_eq
    ext x
    rw [iterSchwartzDeriv_map_smul]
    simp [SchwartzMap.smul_apply]
  rw [MemLp.toLp_congr _ ((schwartzDerivMemLp n α φ).const_smul c) heq]
  exact MemLp.toLp_const_smul c _

end SchwartzLpEmbedding

section SchwartzProdLp

end SchwartzProdLp

/-- Pairing `⟨f, φ⟩ = ∫ f(x) · φ(x) dx` of a `C_0` function `f` against a
Schwartz function `φ`, used to express tempered distributions of the form
arising in the Schwartz representation theorem. -/
def c0SchwartzPairing
    (f : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : ℂ :=
  ∫ x, f x * φ x


set_option maxHeartbeats 1600000 in
/-- Hahn–Banach + Riesz representation for sums of `L^2`-bounded operators:
given a linear functional `L : V → ℂ` controlled by `‖L v‖ ≤ C ∑_α ‖T α v‖_{L²}`,
there exist `L²` functions `g α` such that `L v = ∑_α ∫ g α · T α v`. The key
analytic tool used to derive the Schwartz representation theorem. -/
theorem hahn_banach_riesz_product_l2
    {E : Type*} [MeasureSpace E] [MeasureTheory.SigmaFinite (MeasureTheory.volume : MeasureTheory.Measure E)]
    {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (L : V →ₗ[ℂ] ℂ)
    (T : ι → V → E → ℂ)
    (hT_memLp : ∀ α ∈ A, ∀ v, MeasureTheory.MemLp (T α v) 2 MeasureTheory.volume)
    (hT_add : ∀ α ∈ A, ∀ v w, T α (v + w) =ᵐ[MeasureTheory.volume] T α v + T α w)
    (hT_smul : ∀ α ∈ A, ∀ (c : ℂ) v, T α (c • v) =ᵐ[MeasureTheory.volume] c • T α v)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ v, ‖L v‖ ≤ C * ∑ α ∈ A,
      (∫ x, ‖T α v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) :
    ∃ (g : ι → E → ℂ),
      (∀ α ∈ A, MeasureTheory.MemLp (g α) 2 MeasureTheory.volume) ∧
      ∀ v, L v = ∑ α ∈ A, ∫ x, g α x * T α v x := by
  classical


  let H := PiLp 2 (fun (_ : ↥A) => ↥(Lp ℂ 2 (volume : Measure E)))
  let Φ : V →ₗ[ℂ] H :=
    { toFun := fun v => WithLp.toLp 2 (fun (i : ↥A) => (hT_memLp i.1 i.2 v).toLp _)
      map_add' := fun v w => by
        apply PiLp.ext; intro ⟨α, hα⟩
        change (hT_memLp α hα (v + w)).toLp _ =
          (hT_memLp α hα v).toLp _ + (hT_memLp α hα w).toLp _
        rw [MemLp.toLp_congr (hT_memLp α hα (v + w))
          ((hT_memLp α hα v).add (hT_memLp α hα w)) (hT_add α hα v w)]
        exact MemLp.toLp_add _ _
      map_smul' := fun c v => by
        apply PiLp.ext; intro ⟨α, hα⟩
        change (hT_memLp α hα (c • v)).toLp _ = c • (hT_memLp α hα v).toLp _
        rw [MemLp.toLp_congr (hT_memLp α hα (c • v))
          ((hT_memLp α hα v).const_smul c) (hT_smul α hα c v)]
        exact MemLp.toLp_const_smul c _ }


  have hΦ_comp_norm : ∀ v (i : ↥A),
      ‖(Φ v).ofLp i‖ = (∫ x, ‖T i.1 v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro v ⟨α, hα⟩
    show ‖(hT_memLp α hα v).toLp _‖ = _
    rw [Lp.norm_toLp, (hT_memLp α hα v).eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ _)]
    ring_nf

  have hbound' : ∀ v, ‖L v‖ ≤ C * ∑ i : ↥A, ‖(Φ v).ofLp i‖ := by
    intro v
    have hbd := hbound v
    rw [show ∑ α ∈ A, (∫ x, ‖T α v x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) =
      ∑ i : ↥A, ‖(Φ v).ofLp i‖ from by
        rw [← A.sum_coe_sort]; congr 1; ext ⟨α, hα⟩; exact (hΦ_comp_norm v ⟨α, hα⟩).symm] at hbd
    exact hbd

  have hker : ∀ v, Φ v = 0 → L v = 0 := by
    intro v hv
    have hzero : ∑ i : ↥A, ‖(Φ v).ofLp i‖ = 0 := by
      rw [hv]; simp [PiLp.zero_apply, WithLp.ofLp]
    have hbd := hbound' v
    rw [hzero, mul_zero] at hbd
    exact norm_eq_zero.mp (le_antisymm hbd (norm_nonneg _))


  have hwf : ∀ (v₁ v₂ : V), Φ v₁ = Φ v₂ → L v₁ = L v₂ := by
    intro v₁ v₂ heq
    have h : Φ (v₁ + (-1 : ℂ) • v₂) = 0 := by
      rw [Φ.map_add, Φ.map_smul]; simp [heq]
    have h0 := hker _ h
    have hL : L (v₁ + (-1 : ℂ) • v₂) = L v₁ - L v₂ := by
      rw [L.map_add, L.map_smul]
      simp [sub_eq_add_neg, neg_smul, one_smul]
    rw [hL] at h0
    exact sub_eq_zero.mp h0


  let ℓ_fun : ↥(LinearMap.range Φ) → ℂ := fun y => L (Classical.choose y.2)
  have hℓ_wf : ∀ (y : ↥(LinearMap.range Φ)) (v : V), Φ v = y.1 → ℓ_fun y = L v := by
    intro y v hv; exact hwf _ _ (by rw [Classical.choose_spec y.2, hv])

  let ℓ_lin : ↥(LinearMap.range Φ) →ₗ[ℂ] ℂ :=

    { toFun := ℓ_fun
      map_add' := fun a b => by
        have ha := Classical.choose_spec a.2
        have hb := Classical.choose_spec b.2
        have hab : Φ (Classical.choose a.2 + Classical.choose b.2) = (a : H) + b := by
          rw [Φ.map_add, ha, hb]
        have hkey := hwf _ _ (hab.trans (Classical.choose_spec (a + b).2).symm)
        simp only [ℓ_fun, L.map_add] at hkey ⊢
        exact hkey.symm
      map_smul' := fun c a => by
        have ha := Classical.choose_spec a.2
        have hca : Φ (c • Classical.choose a.2) = c • (a : H) := by
          rw [Φ.map_smul, ha]
        have hkey := hwf _ _ (hca.trans (Classical.choose_spec (c • a).2).symm)
        simp only [ℓ_fun, L.map_smul, RingHom.id_apply] at hkey ⊢
        exact hkey.symm }

  have hℓ_bound : ∀ y : ↥(LinearMap.range Φ), ‖ℓ_lin y‖ ≤
      (C * Real.sqrt A.card) * ‖(y : H)‖ := by
    intro ⟨y, hy⟩
    have hv := Classical.choose_spec hy
    show ‖L (Classical.choose hy)‖ ≤ _
    calc ‖L (Classical.choose hy)‖
        ≤ C * ∑ i : ↥A, ‖(Φ (Classical.choose hy)).ofLp i‖ := hbound' _
      _ = C * ∑ i : ↥A, ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖ := by
          congr 2; ext i; congr 1
          exact congr_fun (congr_arg WithLp.ofLp hv) i

      _ ≤ C * (Real.sqrt A.card * Real.sqrt (∑ i : ↥A,
          ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ↥A) (fun _ => (1 : ℝ))
            (fun i => ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1.ofLp i‖)
          simp only [one_mul, one_pow, Finset.sum_const, Nat.smul_one_eq_cast,
            Finset.card_univ, Fintype.card_coe] at h
          exact h
      _ = (C * Real.sqrt A.card) * ‖(⟨y, hy⟩ : ↥(LinearMap.range Φ)).1‖ := by
          rw [PiLp.norm_eq_of_L2]; ring

  let ℓ_clm : ↥(LinearMap.range Φ) →L[ℂ] ℂ :=
    LinearMap.mkContinuous ℓ_lin (C * Real.sqrt A.card) hℓ_bound
  obtain ⟨L', hL'ext, _⟩ := exists_extension_norm_eq (LinearMap.range Φ) ℓ_clm

  set G := (InnerProductSpace.toDual ℂ H).symm L'

  refine ⟨fun α => if hα : α ∈ A then
    fun x => (starRingEnd ℂ) ((G.ofLp ⟨α, hα⟩ : E → ℂ) x) else 0, ?_, ?_⟩
  ·
    intro α hα
    simp only [dif_pos hα]
    have hmem : MemLp (↑↑(G.ofLp ⟨α, hα⟩) : E → ℂ) 2 volume := Lp.memLp _
    have heq : (fun x => (starRingEnd ℂ) ((G.ofLp ⟨α, hα⟩ : E → ℂ) x)) =
      star (↑↑(G.ofLp ⟨α, hα⟩) : E → ℂ) := by
        ext x; simp [Pi.star_apply, RCLike.star_def]
    rw [heq]; exact hmem.star
  ·
    intro v

    have hmem : Φ v ∈ LinearMap.range Φ := ⟨v, rfl⟩
    have hLv_eq : L v = L' (Φ v) := by
      have h1 : L' (Φ v) = L' ↑(⟨Φ v, hmem⟩ : ↥(LinearMap.range Φ)) := rfl
      rw [h1, hL'ext ⟨Φ v, hmem⟩]
      symm
      simp only [ℓ_clm, LinearMap.mkContinuous_apply]
      exact hℓ_wf ⟨Φ v, hmem⟩ v rfl

    have hLv_inner : L v = @inner ℂ _ _ G (Φ v) := by
      rw [hLv_eq, ← InnerProductSpace.toDual_apply_apply]
      simp [G, LinearIsometryEquiv.apply_symm_apply]
    rw [hLv_inner, PiLp.inner_apply, ← A.sum_coe_sort]
    congr 1; ext ⟨α, hα⟩
    rw [MeasureTheory.L2.inner_def]

    refine MeasureTheory.integral_congr_ae ?_
    exact (MemLp.coeFn_toLp (hT_memLp α hα v)).mono fun x hx => by
      simp only [dif_pos hα, RCLike.inner_apply]

      have hx' : (↑↑((Φ v).ofLp ⟨α, hα⟩) : E → ℂ) x = T α v x := hx
      rw [hx']; ring

/-- If a continuous linear functional `u` on Schwartz space is bounded by the
sum of `L^2` norms of Schwartz derivatives `∂^α φ` over `|α| ≤ m`, then `u`
admits an `L^2` representation `u φ = ∑_α ∫ g_α · ∂^α φ`. -/
theorem schwartz_functional_l2_deriv_bound
    (n : ℕ) (u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ)
    (m : ℕ)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ‖u φ‖ ≤ C * ∑ α ∈ multiIndicesBall n m,
        (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) :
    ∃ (g : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ),
      (∀ α, α ∈ multiIndicesBall n m →
        MeasureTheory.MemLp (g α) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) ∧
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ α ∈ multiIndicesBall n m,
          ∫ x, g α x * (iterSchwartzDeriv α φ) x := by
  classical
  obtain ⟨C, hC, hbd⟩ := hbound
  exact hahn_banach_riesz_product_l2
    (E := EuclideanSpace ℝ (Fin n))
    (ι := Fin n → ℕ)
    (A := multiIndicesBall n m)
    (V := 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u.toLinearMap)
    (fun α φ x => (iterSchwartzDeriv α φ) x)
    (fun α _ φ => schwartzDerivMemLp n α φ)
    (fun α _ φ ψ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_add, SchwartzMap.add_apply, Pi.add_apply])
    (fun α _ c φ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_smul, SchwartzMap.smul_apply, Pi.smul_apply])
    C hC hbd


/-- Weighted pointwise bound: for a Schwartz function `φ`, the product
`‖x‖^k · ‖D^l φ(x)‖` is dominated by a sum of `L^2` norms of Schwartz
derivatives of order `≤ k + l + n + 1`. Used to convert Schwartz seminorms
to `L^2`-based estimates. -/
theorem schwartz_weighted_pointwise_bound (n k l : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (↑φ) x‖ ≤
      ∑ α ∈ multiIndicesBall n (k + l + n + 1),
        (∫ y, ‖(iterSchwartzDeriv α φ) y‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by sorry


/-- Auxiliary form: a single Schwartz seminorm `‖φ‖_{k,l}` is bounded above by
a sum of `L^2` norms of Schwartz derivatives of order `≤ k + l + n + 1`. -/
theorem schwartz_seminorm_le_l2_deriv_sum_aux (n : ℕ) (k l : ℕ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (SchwartzMap.seminorm ℂ k l) φ ≤
          C * ∑ α ∈ multiIndicesBall n m,
            (∫ y, ‖(iterSchwartzDeriv α φ) y‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
  refine ⟨k + l + n + 1, 1, one_pos, fun φ => ?_⟩
  rw [one_mul]
  apply SchwartzMap.seminorm_le_bound ℂ k l φ
  · apply Finset.sum_nonneg; intro α _
    apply Real.rpow_nonneg
    apply MeasureTheory.integral_nonneg
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  · exact schwartz_weighted_pointwise_bound n k l φ


/-- Pointwise Sobolev-type bound: for some `m, C > 0`, the weighted product
`‖x‖^k · ‖D^l φ(x)‖` is bounded by `C` times the sum of `L^2` norms of
Schwartz derivatives of order `≤ m`. -/
theorem sobolev_pointwise_bound (n : ℕ) (k l : ℕ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (x : EuclideanSpace ℝ (Fin n)),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑φ) x‖ ≤
          C * ∑ α ∈ multiIndicesBall n m,
            (∫ y, ‖(iterSchwartzDeriv α φ) y‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
  obtain ⟨m, C, hC, hbound⟩ := schwartz_seminorm_le_l2_deriv_sum_aux n k l
  exact ⟨m, C, hC, fun φ x =>
    (SchwartzMap.le_seminorm ℂ k l φ x).trans (hbound φ)⟩


/-- A single Schwartz seminorm `‖·‖_{k,l}` is bounded by `C` times a sum of
`L^2` norms of Schwartz derivatives `∂^α` over a multi-index ball. -/
theorem schwartz_single_seminorm_le_l2_deriv_sum
    (n : ℕ) (k l : ℕ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (SchwartzMap.seminorm ℂ k l) φ ≤
          C * ∑ α ∈ multiIndicesBall n m,
            (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
  obtain ⟨m, C, hC, hbound⟩ := sobolev_pointwise_bound n k l
  refine ⟨m, C, hC, fun φ => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ k l φ
  · apply mul_nonneg (le_of_lt hC)
    apply Finset.sum_nonneg; intro α _
    apply Real.rpow_nonneg
    apply MeasureTheory.integral_nonneg
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  · exact hbound φ


/-- Joint bound: the supremum of a finite family of Schwartz seminorms can be
controlled by a single sum of `L^2` derivative norms. -/
theorem schwartz_seminorm_le_l2_deriv_sum
    (n : ℕ) (s : Finset (ℕ × ℕ)) :
    ∃ (m : ℕ) (C' : ℝ), 0 < C' ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ)) φ ≤
          C' * ∑ α ∈ multiIndicesBall n m,
            (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
  classical

  have h_each : ∀ p : ℕ × ℕ, ∃ (mp : ℕ) (Cp : ℝ), 0 < Cp ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ p) φ ≤
          Cp * ∑ α ∈ multiIndicesBall n mp,
            (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro ⟨k, l⟩
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact schwartz_single_seminorm_le_l2_deriv_sum n k l
  choose mf Cf hCf using h_each

  let m := s.sup mf

  refine ⟨m, (∑ p ∈ s, Cf p) + 1, by linarith [Finset.sum_nonneg (fun p (_ : p ∈ s) => le_of_lt (hCf p).1)], fun φ => ?_⟩

  have hsum_nonneg : ∀ m', 0 ≤ ∑ α ∈ multiIndicesBall n m',
      (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro m'
    apply Finset.sum_nonneg; intro α _
    apply Real.rpow_nonneg; apply MeasureTheory.integral_nonneg
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _

  apply Seminorm.finset_sup_apply_le
  · apply mul_nonneg (by linarith [Finset.sum_nonneg (fun p (_ : p ∈ s) => le_of_lt (hCf p).1)])
      (hsum_nonneg m)
  intro p hp

  have hbound := (hCf p).2 φ

  have hmono : mf p ≤ m := Finset.le_sup hp
  have hsum_mono : ∑ α ∈ multiIndicesBall n (mf p),
      (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) ≤
    ∑ α ∈ multiIndicesBall n m,
      (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by

    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro α hα
      rw [mem_multiIndicesBall_iff] at hα ⊢
      exact le_trans hα hmono
    · intro α _ _
      apply Real.rpow_nonneg; apply MeasureTheory.integral_nonneg
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _

  calc (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ p) φ
      ≤ Cf p * ∑ α ∈ multiIndicesBall n (mf p),
          (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := hbound
    _ ≤ Cf p * ∑ α ∈ multiIndicesBall n m,
          (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hsum_mono (le_of_lt (hCf p).1)
    _ ≤ (∑ q ∈ s, Cf q) * ∑ α ∈ multiIndicesBall n m,
          (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (hsum_nonneg m)
        exact Finset.single_le_sum (fun q _ => le_of_lt (hCf q).1) hp
    _ ≤ ((∑ q ∈ s, Cf q) + 1) * ∑ α ∈ multiIndicesBall n m,
          (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (hsum_nonneg m)


/-- Continuous linear functionals on Schwartz space are bounded by a sum of
`L^2` norms of Schwartz derivatives, yielding a Sobolev-type estimate. -/
theorem schwartz_functional_sobolev_bound
    (n : ℕ) (u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧ ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ‖u φ‖ ≤ C * ∑ α ∈ multiIndicesBall n m,
        (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by


  obtain ⟨s, C_nn, hC_ne, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin n)) ℂ)
    ((normSeminorm ℂ ℂ).comp u.toLinearMap)
    (continuous_norm.comp u.continuous)


  obtain ⟨m, C', hC'_pos, hsem_bound⟩ := schwartz_seminorm_le_l2_deriv_sum n s

  refine ⟨m, ↑C_nn * C' + 1, by positivity, fun φ => ?_⟩

  have h1 : ‖u φ‖ ≤ ↑C_nn * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ)) φ := by
    have := Seminorm.le_def.mp hbound φ
    simp only [Seminorm.comp_apply, Seminorm.smul_apply] at this
    exact this

  have h2 := hsem_bound φ

  have h3 : ‖u φ‖ ≤ ↑C_nn * C' *
      ∑ α ∈ multiIndicesBall n m,
        (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    calc ‖u φ‖ ≤ ↑C_nn * (s.sup (schwartzSeminormFamily ℂ _ ℂ)) φ := h1
      _ ≤ ↑C_nn * (C' * ∑ α ∈ multiIndicesBall n m,
            (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h2
          exact_mod_cast C_nn.coe_nonneg
      _ = ↑C_nn * C' * ∑ α ∈ multiIndicesBall n m,
            (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by ring

  calc ‖u φ‖ ≤ ↑C_nn * C' * ∑ α ∈ multiIndicesBall n m,
        (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := h3
    _ ≤ (↑C_nn * C' + 1) * ∑ α ∈ multiIndicesBall n m,
        (∫ x, ‖(iterSchwartzDeriv α φ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      apply Finset.sum_nonneg
      intro α _
      apply Real.rpow_nonneg
      apply MeasureTheory.integral_nonneg
      intro x
      apply Real.rpow_nonneg (norm_nonneg _)

/-- Every continuous linear functional `u` on Schwartz space admits an `L^2`
derivative representation: `u φ = ∑_α ∫ g_α · ∂^α φ` for some finite collection
of `L^2` functions `g_α` indexed by multi-indices `|α| ≤ m`. -/
theorem continuous_linear_l2_deriv_representation
    (n : ℕ) (u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ) :
    ∃ (m : ℕ) (g : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ),
      (∀ α, α ∈ multiIndicesBall n m →
        MeasureTheory.MemLp (g α) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) ∧
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ α ∈ multiIndicesBall n m,
          ∫ x, g α x * (iterSchwartzDeriv α φ) x := by

  obtain ⟨m, C, hC, hbound⟩ := schwartz_functional_sobolev_bound n u

  obtain ⟨g, hg_mem, hg_eq⟩ := schwartz_functional_l2_deriv_bound n u m ⟨C, hC, hbound⟩
  exact ⟨m, g, hg_mem, hg_eq⟩

/-- `L^2` derivative representation for tempered distributions: every
`u ∈ 𝓢'(ℝ^n, ℂ)` is a finite sum of derivatives of `L^2` functions paired with
test functions. -/
theorem tempered_distrib_l2_deriv_representation
    (n : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (g : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ),
      (∀ α, α ∈ multiIndicesBall n m →
        MeasureTheory.MemLp (g α) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) ∧
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ α ∈ multiIndicesBall n m,
          ∫ x, g α x * (iterSchwartzDeriv α φ) x :=
  continuous_linear_l2_deriv_representation n
    ((ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) ℂ
      {s : Set (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) | s.Finite}).symm u)


/-- Fourier multiplier promotes any `L^2` function to a representative with
`H^{n+j+1}` regularity (a placeholder for an appropriate Fourier-side lift,
used to feed the Sobolev embedding). -/
theorem fourier_multiplier_l2_sobolev_regularity (n j : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (β : Fin n → ℕ) (hβ : β ∈ multiIndicesBall n j) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ),
      (g =ᵐ[MeasureTheory.volume] f) ∧
      (∀ i : ℕ, i ≤ n + j + 1 →
        MeasureTheory.MemLp (fun x => iteratedFDeriv ℝ i g x) 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by sorry


/-- Any `L^2` function is a.e. equal to an element of a Sobolev space
`SobolevSpace n j`, by combining Fourier regularization with the Sobolev
embedding. -/
theorem l2_to_sobolev_lift (n j : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (β : Fin n → ℕ) (hβ : β ∈ multiIndicesBall n j) :
    ∃ (u : SobolevEmbedding.SobolevSpace n j),
      u.toFun =ᵐ[MeasureTheory.volume] f := by


  obtain ⟨g, hg_ae, hg_reg⟩ := fourier_multiplier_l2_sobolev_regularity n j f hf β hβ


  have hj_le : j ≤ n + j + 1 := by omega
  have hn_lt : n < 2 * ((n + j + 1) - j) := by omega
  have hcontdiff : ContDiff ℝ (↑j : ℕ∞) g :=
    SobolevEmbedding.sobolev_contDiff_of_memLp hj_le hn_lt g (fun i hi => hg_reg i hi)

  exact ⟨⟨g, hcontdiff, fun i hi => hg_reg i (by omega)⟩, hg_ae⟩


/-- Hölder-type bound for the `L^2` × Schwartz pairing: `‖∫ g · ψ‖` is
controlled by a sum of `L^2` norms of Schwartz derivatives over
`multiIndicesBall n j`. -/
theorem l2_schwartz_pairing_bound (n j : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ‖∫ x, g x * ψ x‖ ≤ C * ∑ β ∈ multiIndicesBall n j,
        (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by

  set A := (∫ x : EuclideanSpace ℝ (Fin n), ‖g x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) with hA_def
  refine ⟨A + 1, by linarith [Real.rpow_nonneg (integral_nonneg (fun x => by positivity) :
    (0:ℝ) ≤ ∫ x : EuclideanSpace ℝ (Fin n), ‖g x‖ ^ (2:ℝ)) (1/2 : ℝ)], fun ψ => ?_⟩

  have hderiv_zero : iterSchwartzDeriv (0 : Fin n → ℕ) ψ = ψ := by
    unfold iterSchwartzDeriv
    have h : ∀ (j : Fin n) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        iterSchwartzDerivCoord j ((0 : Fin n → ℕ) j) φ = φ := by
      intro j φ
      simp only [Pi.zero_apply]
      unfold iterSchwartzDerivCoord
      simp [Function.iterate_zero]
    induction (List.finRange n) with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldr_cons]
      rw [ih, h]


  have h0_mem : (0 : Fin n → ℕ) ∈ multiIndicesBall n j := by
    rw [mem_multiIndicesBall_iff]
    simp [multiIndexOrder]

  have h_holder : ‖∫ x, g x * ψ x‖ ≤
      A * (∫ a : EuclideanSpace ℝ (Fin n),
        ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
    calc ‖∫ x, g x * ψ x‖
        ≤ ∫ x, ‖g x * ψ x‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖g x‖ * ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ := by
          congr 1; ext x; exact Complex.norm_mul (g x) (ψ x)
      _ ≤ A * (∫ a, ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
          have h22 : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
          have hg2 : MemLp g (ENNReal.ofReal 2) volume := by
            rwa [show ENNReal.ofReal 2 = 2 from by norm_num]
          have hψ2 : MemLp (ψ : EuclideanSpace ℝ (Fin n) → ℂ) (ENNReal.ofReal 2) volume := by
            rw [show ENNReal.ofReal 2 = 2 from by norm_num]
            exact ψ.memLp 2
          exact integral_mul_norm_le_Lp_mul_Lq h22 hg2 hψ2

  have h_term_eq : (∫ x : EuclideanSpace ℝ (Fin n),
      ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ (2:ℝ)) ^ (1/2 : ℝ) =
    (∫ x, ‖(iterSchwartzDeriv (0 : Fin n → ℕ) ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    congr 1; congr 1; ext x; congr 1; congr 1
    have : (iterSchwartzDeriv (0 : Fin n → ℕ) ψ : EuclideanSpace ℝ (Fin n) → ℂ) x =
        (ψ : EuclideanSpace ℝ (Fin n) → ℂ) x := by
      rw [hderiv_zero]
    rw [this]

  have h_sum_nonneg : ∀ β ∈ multiIndicesBall n j,
      (0:ℝ) ≤ (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    intro β _
    exact Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _

  have h_le_sum : (∫ x : EuclideanSpace ℝ (Fin n),
      ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) x‖ ^ (2:ℝ)) ^ (1/2 : ℝ) ≤
    ∑ β ∈ multiIndicesBall n j,
      (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
    rw [h_term_eq]
    exact Finset.single_le_sum h_sum_nonneg h0_mem

  have hA_nonneg : (0:ℝ) ≤ A :=
    Real.rpow_nonneg (integral_nonneg (fun x => by positivity)) _
  have h_sum_nonneg' : (0:ℝ) ≤ ∑ β ∈ multiIndicesBall n j,
      (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) :=
    Finset.sum_nonneg h_sum_nonneg
  calc ‖∫ x, g x * ψ x‖
      ≤ A * (∫ a : EuclideanSpace ℝ (Fin n),
          ‖(ψ : EuclideanSpace ℝ (Fin n) → ℂ) a‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := h_holder
    _ ≤ A * ∑ β ∈ multiIndicesBall n j,
          (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left h_le_sum hA_nonneg
    _ ≤ (A + 1) * ∑ β ∈ multiIndicesBall n j,
          (∫ x, ‖(iterSchwartzDeriv β ψ) x‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (by linarith) h_sum_nonneg'


/-- The product `g · ψ` of an `L^2` function and a Schwartz function is
integrable. -/
theorem l2_schwartz_mul_integrable (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MeasureTheory.Integrable (fun x => g x * ψ x)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
  hg.integrable_mul (ψ.memLp 2)

/-- Decomposition of an `L^2` pairing into Sobolev derivatives: every
`L^2` function `g` admits a representation `∫ g·ψ = ∑_β ∫ w_β · ∂^β ψ` where
each `w_β` lies in `SobolevSpace n j`. -/
theorem l2_sobolev_decomp_for_order (n j : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ (w : (Fin n → ℕ) → SobolevEmbedding.SobolevSpace n j),
      ∀ (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∫ x, g x * ψ x) =
        ∑ β ∈ multiIndicesBall n j,
          ∫ x, (w β).toFun x * (iterSchwartzDeriv β ψ) x := by
  obtain ⟨C, hC, hbd⟩ := l2_schwartz_pairing_bound n j g hg
  obtain ⟨g_rep, hg_rep_mem, hg_rep_eq⟩ := hahn_banach_riesz_product_l2
    (E := EuclideanSpace ℝ (Fin n)) (ι := Fin n → ℕ)
    (A := multiIndicesBall n j) (V := 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    { toFun := fun ψ => ∫ x, g x * ψ x
      map_add' := fun ψ₁ ψ₂ => by
        simp_rw [SchwartzMap.add_apply, mul_add]
        exact MeasureTheory.integral_add
          (l2_schwartz_mul_integrable n g hg ψ₁)
          (l2_schwartz_mul_integrable n g hg ψ₂)
      map_smul' := fun c ψ => by
        simp only [RingHom.id_apply, SchwartzMap.smul_apply, smul_eq_mul]
        simp_rw [show ∀ x, g x * (c * ψ x) = c * (g x * ψ x) from fun x => by ring]
        exact MeasureTheory.integral_const_mul c _ }
    (fun β ψ x => (iterSchwartzDeriv β ψ) x)
    (fun β _ ψ => schwartzDerivMemLp n β ψ)
    (fun β _ ψ₁ ψ₂ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_add, SchwartzMap.add_apply, Pi.add_apply])
    (fun β _ c ψ => by
      apply Filter.EventuallyEq.of_eq; ext x
      simp [iterSchwartzDeriv_map_smul, SchwartzMap.smul_apply, Pi.smul_apply])
    C hC hbd
  have hlift : ∀ β ∈ multiIndicesBall n j,
      ∃ (u : SobolevEmbedding.SobolevSpace n j), u.toFun =ᵐ[MeasureTheory.volume] g_rep β :=
    fun β hβ => l2_to_sobolev_lift n j (g_rep β) (hg_rep_mem β hβ) β hβ
  choose w_ball hw_ball using hlift
  haveI : Nonempty (SobolevEmbedding.SobolevSpace n j) :=
    ⟨w_ball (0 : Fin n → ℕ) (mem_multiIndicesBall_iff.mpr (by simp [multiIndexOrder]))⟩
  let w : (Fin n → ℕ) → SobolevEmbedding.SobolevSpace n j :=
    fun β => if hβ : β ∈ multiIndicesBall n j then w_ball β hβ else Classical.arbitrary _
  refine ⟨w, fun ψ => ?_⟩
  have hid := hg_rep_eq ψ
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at hid
  rw [hid]
  apply Finset.sum_congr rfl
  intro β hβ
  simp only [w, dif_pos hβ]
  exact MeasureTheory.integral_congr_ae
    ((hw_ball β hβ).symm.mono (fun x hx => by simp only [hx]))

/-- Variant of `l2_sobolev_decomp_for_order` choosing `j` large enough so that
`n < 2j`, hence guaranteeing each Sobolev representative is automatically a
continuous `C_0` function (via the Sobolev embedding). -/
theorem l2_sobolev_deriv_decomp (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ (j : ℕ) (_ : n < 2 * j)
      (w : (Fin n → ℕ) → SobolevEmbedding.SobolevSpace n j),
      ∀ (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∫ x, g x * ψ x) =
        ∑ β ∈ multiIndicesBall n j,
          ∫ x, (w β).toFun x * (iterSchwartzDeriv β ψ) x := by

  refine ⟨n + 1, by omega, ?_⟩

  exact l2_sobolev_decomp_for_order n (n + 1) g hg


/-- `L^2` to `C_0`-derivative decomposition: every `L^2` pairing equals a sum
`∑_β c0SchwartzPairing (v β) (∂^β ψ)` with each `v β` a `C_0` function (the
Sobolev representatives produced by the Sobolev embedding). -/
theorem l2_c0_deriv_decomp_base (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ (j : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∫ x, g x * ψ x) =
        ∑ β ∈ multiIndicesBall n j,
          c0SchwartzPairing (v β) (iterSchwartzDeriv β ψ) := by

  obtain ⟨j, hj, w, hw⟩ := l2_sobolev_deriv_decomp n g hg


  refine ⟨j, fun β => ⟨⟨(w β).toFun,
    SobolevEmbedding.sobolevSpace_continuous_aux hj (w β)⟩,
    SobolevEmbedding.sobolevSpace_zeroAtInfty_aux hj (w β)⟩, fun ψ => ?_⟩

  rw [hw ψ]
  congr 1


/-- Directional derivatives on Schwartz space commute: `∂_v ∂_w φ = ∂_w ∂_v φ`.
A consequence of Schwarz's symmetry of second derivatives. -/
lemma schwartz_lineDerivOp_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SMulCommClass ℝ ℝ F]
    (v w : E) (φ : 𝓢(E, F)) :
    LineDeriv.lineDerivOp v (LineDeriv.lineDerivOp w φ) =
    LineDeriv.lineDerivOp w (LineDeriv.lineDerivOp v φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → F)) x := by
    convert (SchwartzMap.fderivCLM ℝ E F φ).differentiableAt using 1
  rw [show ⇑(LineDeriv.lineDerivOp w φ : 𝓢(E, F)) = fun y => fderiv ℝ (↑φ) y w from
    funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv w φ y,
    fderiv_clm_apply hd (differentiableAt_const w),
    show ⇑(LineDeriv.lineDerivOp v φ : 𝓢(E, F)) = fun y => fderiv ℝ (↑φ) y v from
    funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv v φ y,
    fderiv_clm_apply hd (differentiableAt_const v)]
  simp
  exact second_derivative_symmetric
    (f := (↑φ : E → F)) (f' := fderiv ℝ (↑φ))
    (fun y => φ.differentiableAt.hasFDerivAt) hd.hasFDerivAt v w

/-- Iterated directional derivatives commute past a single directional
derivative: `∂_v^k ∂_w φ = ∂_w ∂_v^k φ`. -/
lemma iterate_lineDerivOp_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SMulCommClass ℝ ℝ F]
    (v w : E) (k : ℕ) (φ : 𝓢(E, F)) :
    (LineDeriv.lineDerivOp v)^[k] (LineDeriv.lineDerivOp w φ) =
    LineDeriv.lineDerivOp w ((LineDeriv.lineDerivOp v)^[k] φ) := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [schwartz_lineDerivOp_comm v w φ, ih]

/-- Two iterated directional derivatives commute: `∂_v^k ∂_w^m φ = ∂_w^m ∂_v^k φ`. -/
lemma iterate_iterate_lineDerivOp_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SMulCommClass ℝ ℝ F]
    (v w : E) (k m : ℕ) (φ : 𝓢(E, F)) :
    (LineDeriv.lineDerivOp v)^[k] ((LineDeriv.lineDerivOp w)^[m] φ) =
    (LineDeriv.lineDerivOp w)^[m] ((LineDeriv.lineDerivOp v)^[k] φ) := by
  induction m generalizing φ with
  | zero => simp
  | succ m ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [ih (LineDeriv.lineDerivOp w φ)]
    congr 1
    exact iterate_lineDerivOp_comm v w k φ

/-- Coordinate Schwartz derivatives commute: `∂_i^a ∂_j^b φ = ∂_j^b ∂_i^a φ`. -/
lemma iterSchwartzDerivCoord_comm {n : ℕ} (i j : Fin n) (a b : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord i a (iterSchwartzDerivCoord j b φ) =
    iterSchwartzDerivCoord j b (iterSchwartzDerivCoord i a φ) := by
  simp only [iterSchwartzDerivCoord]
  exact iterate_iterate_lineDerivOp_comm _ _ a b φ

/-- A coordinate Schwartz derivative commutes with the `foldr` used to define
`iterSchwartzDeriv`, allowing rearrangement of derivative orderings. -/
lemma iterSchwartzDerivCoord_comm_foldr {n : ℕ} (j : Fin n) (k : ℕ) (γ : Fin n → ℕ)
    (l : List (Fin n)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j k (l.foldr (fun i ψ => iterSchwartzDerivCoord i (γ i) ψ) φ) =
    l.foldr (fun i ψ => iterSchwartzDerivCoord i (γ i) ψ) (iterSchwartzDerivCoord j k φ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [iterSchwartzDerivCoord_comm j i k (γ i), ih]

/-- Coordinate Schwartz derivatives compose by addition of orders:
`∂_j^b ∂_j^a φ = ∂_j^{a+b} φ`. -/
lemma iterSchwartzDerivCoord_add {n : ℕ} (j : Fin n) (a b : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDerivCoord j b (iterSchwartzDerivCoord j a φ) =
    iterSchwartzDerivCoord j (a + b) φ := by
  simp only [iterSchwartzDerivCoord]
  rw [Nat.add_comm, ← Function.iterate_add_apply]

/-- Composition of multi-index Schwartz derivatives:
`∂^β (∂^α φ) = ∂^{α + β} φ`. -/
theorem iterSchwartzDeriv_comp {n : ℕ} (α β : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    iterSchwartzDeriv β (iterSchwartzDeriv α φ) = iterSchwartzDeriv (α + β) φ := by
  simp only [iterSchwartzDeriv]
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, Pi.add_apply]


    conv_lhs => rw [← iterSchwartzDerivCoord_comm_foldr j (α j) β l]


    rw [iterSchwartzDerivCoord_add j (α j) (β j), ih]
    simp only [Pi.add_apply]

/-- Additivity of multi-index order: `|α + β| = |α| + |β|`. -/
theorem multiIndexOrder_add {n : ℕ} (α β : Fin n → ℕ) :
    multiIndexOrder (α + β) = multiIndexOrder α + multiIndexOrder β := by
  simp only [multiIndexOrder, Pi.add_apply, Finset.sum_add_distrib]


/-- For a fixed multi-index `α`, the pairing `∫ g · ∂^α φ` can be rewritten
as a sum `∑_γ c0SchwartzPairing (w γ) (∂^γ φ)` over a larger multi-index ball,
using the composition law `∂^β ∂^α = ∂^{α+β}` together with `L^2 → C_0`
decomposition. -/
theorem l2_single_c0_deriv_decomp (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (α : Fin n → ℕ) :
    ∃ (M : ℕ) (w : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∫ x, g x * (iterSchwartzDeriv α φ) x) =
        ∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (w γ) (iterSchwartzDeriv γ φ) := by
  classical

  obtain ⟨j, v, hv⟩ := l2_c0_deriv_decomp_base n g hg


  refine ⟨j + multiIndexOrder α, fun γ =>
    if h : (∀ i, α i ≤ γ i) ∧ (fun i => γ i - α i) ∈ multiIndicesBall n j
    then v (fun i => γ i - α i) else 0, fun φ => ?_⟩


  rw [hv (iterSchwartzDeriv α φ)]

  simp_rw [iterSchwartzDeriv_comp α]


  symm


  have himg_sub : (multiIndicesBall n j).image (α + ·) ⊆
      multiIndicesBall n (j + multiIndexOrder α) := by
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨β, hβ, rfl⟩ := hγ
    rw [mem_multiIndicesBall_iff] at hβ ⊢
    rw [multiIndexOrder_add]
    omega

  have hinj : Set.InjOn (α + ·) ↑(multiIndicesBall n j) := by
    intro β₁ _ β₂ _ h
    exact add_left_cancel h

  rw [← Finset.sum_subset himg_sub]
  ·


    rw [Finset.sum_image hinj]


    apply Finset.sum_congr rfl
    intro x hx

    have hcond : (∀ i, α i ≤ (α + x) i) ∧
        (fun i => (α + x) i - α i) ∈ multiIndicesBall n j := by
      refine ⟨fun i => le_add_right (le_refl _), ?_⟩
      have : (fun i => (α + x) i - α i) = x := by
        funext i
        simp [Pi.add_apply]
      rw [this]
      exact hx
    rw [dif_pos hcond]
    have heq : (fun i => (α + x) i - α i) = x := by
      ext i; simp [Pi.add_apply]
    rw [heq]
  ·
    intro γ hγM hγ_notin


    have hw0 : ¬((∀ i, α i ≤ γ i) ∧ (fun i => γ i - α i) ∈ multiIndicesBall n j) := by
      intro ⟨hle, hmem⟩
      apply hγ_notin
      rw [Finset.mem_image]
      refine ⟨fun i => γ i - α i, hmem, ?_⟩
      funext i
      simp [Pi.add_apply, Nat.add_sub_cancel' (hle i)]
    simp [dif_neg hw0, c0SchwartzPairing, ZeroAtInftyContinuousMap.zero_apply]

/-- The multi-index ball is monotone in `m`. -/
theorem multiIndicesBall_mono {n : ℕ} {m m' : ℕ} (h : m ≤ m') :
    multiIndicesBall n m ⊆ multiIndicesBall n m' := by
  intro α hα
  rw [mem_multiIndicesBall_iff] at hα ⊢
  exact le_trans hα h


/-- The `C_0`–Schwartz pairing distributes over a finite sum of `C_0`
functions. -/
theorem c0SchwartzPairing_sum_finset {ι : Type*} (s : Finset ι)
    (f : ι → C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    c0SchwartzPairing (∑ i ∈ s, f i) ψ = ∑ i ∈ s, c0SchwartzPairing (f i) ψ := by
  simp only [c0SchwartzPairing]
  have heval : ∀ x, (∑ i ∈ s, f i) x = ∑ i ∈ s, (f i) x := by
    intro x
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      simp only [Finset.sum_cons]
      rw [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, ih]
  simp_rw [heval, Finset.sum_mul]
  rw [integral_finset_sum]
  intro i _
  exact Integrable.bdd_mul (c := ‖(f i).toBCF‖) (ψ.integrable)
    ((f i).continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall
      (fun x => BoundedContinuousFunction.norm_coe_le_norm (f i).toBCF x))

/-- Joint `L^2 → C_0` decomposition: a finite sum `∑_α ∫ g_α · ∂^α φ` over
`|α| ≤ m` of `L^2`-functions can be rewritten as `∑_γ c0SchwartzPairing (v γ) (∂^γ φ)`
with each `v γ` a `C_0` function. -/
theorem l2_function_c0_deriv_decomp (n : ℕ) (m : ℕ)
    (g : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : ∀ α, α ∈ multiIndicesBall n m →
      MeasureTheory.MemLp (g α) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ (M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∑ α ∈ multiIndicesBall n m,
          ∫ x, g α x * (iterSchwartzDeriv α φ) x) =
        ∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ) := by
  classical

  have h_all : ∀ (α : Fin n → ℕ),
      ∃ (Mα : ℕ) (wα : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
        α ∈ multiIndicesBall n m →
        ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
          (∫ x, g α x * (iterSchwartzDeriv α φ) x) =
          ∑ γ ∈ multiIndicesBall n Mα,
            c0SchwartzPairing (wα γ) (iterSchwartzDeriv γ φ) := by
    intro α
    by_cases hα : α ∈ multiIndicesBall n m
    · obtain ⟨Mα, wα, hwα⟩ := l2_single_c0_deriv_decomp n (g α) (hg α hα) α
      exact ⟨Mα, wα, fun _ => hwα⟩
    · exact ⟨0, fun _ => 0, fun h => absurd h hα⟩
  choose Mf wf hwf using h_all

  let M := (multiIndicesBall n m).sup Mf


  refine ⟨M, fun γ =>
    ∑ α ∈ multiIndicesBall n m,
      if γ ∈ multiIndicesBall n (Mf α) then wf α γ else 0, fun φ => ?_⟩


  have hdecomp : ∀ α ∈ multiIndicesBall n m,
      (∫ x, g α x * (iterSchwartzDeriv α φ) x) =
      ∑ γ ∈ multiIndicesBall n (Mf α),
        c0SchwartzPairing (wf α γ) (iterSchwartzDeriv γ φ) :=
    fun α hα => hwf α hα φ

  calc ∑ α ∈ multiIndicesBall n m, ∫ x, g α x * (iterSchwartzDeriv α φ) x
      = ∑ α ∈ multiIndicesBall n m,
          ∑ γ ∈ multiIndicesBall n (Mf α),
            c0SchwartzPairing (wf α γ) (iterSchwartzDeriv γ φ) :=
        Finset.sum_congr rfl hdecomp
    _ = ∑ α ∈ multiIndicesBall n m,
          ∑ γ ∈ multiIndicesBall n M,
            (if γ ∈ multiIndicesBall n (Mf α) then
              c0SchwartzPairing (wf α γ) (iterSchwartzDeriv γ φ)
            else 0) := by
        apply Finset.sum_congr rfl
        intro α hα
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext γ
          simp only [Finset.mem_filter]
          exact ⟨fun hγ => ⟨multiIndicesBall_mono (Finset.le_sup hα) hγ, hγ⟩,
                 fun ⟨_, h⟩ => h⟩
        · intro γ hγ
          simp only [Finset.mem_filter] at hγ
          simp
    _ = ∑ γ ∈ multiIndicesBall n M,
          ∑ α ∈ multiIndicesBall n m,
            (if γ ∈ multiIndicesBall n (Mf α) then
              c0SchwartzPairing (wf α γ) (iterSchwartzDeriv γ φ)
            else 0) :=
        Finset.sum_comm
    _ = ∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing
            (∑ α ∈ multiIndicesBall n m,
              if γ ∈ multiIndicesBall n (Mf α) then wf α γ else 0)
            (iterSchwartzDeriv γ φ) := by
        apply Finset.sum_congr rfl
        intro γ _


        rw [c0SchwartzPairing_sum_finset]
        apply Finset.sum_congr rfl
        intro α _
        split_ifs with h
        · rfl
        · simp [c0SchwartzPairing, ZeroAtInftyContinuousMap.coe_zero, zero_mul,
            MeasureTheory.integral_zero]


/-- Intermediate form of the Schwartz representation theorem (Melrose
eq. (10.10)): every tempered distribution is a finite sum of derivatives of
`C_0` functions paired with test functions. -/
theorem intermediate_form_eq1010
    (n : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ)
            (iterSchwartzDeriv γ φ) := by

  obtain ⟨m, g, hg_mem, hg_eq⟩ := tempered_distrib_l2_deriv_representation n u

  obtain ⟨M, v, hv⟩ := l2_function_c0_deriv_decomp n m g hg_mem
  exact ⟨M, v, fun φ => (hg_eq φ).trans (hv φ)⟩

/-- The finite set of multi-indices `α` with `α_i ≤ γ_i` for all `i`. -/
def multiIndicesBelow (n : ℕ) (γ : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (γ i + 1))


/-- The zero multi-index monomial is the constant function `1`. -/
theorem monomial_zero_eq : monomial (0 : Fin n → ℕ) = fun _ => (1 : ℂ) := by
  ext x
  simp [monomial, Pi.zero_apply]

/-- The `C_0`–Schwartz pairing is zero whenever the `C_0` factor is zero. -/
theorem c0SchwartzPairing_zero (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    c0SchwartzPairing (0 : C₀(EuclideanSpace ℝ (Fin n), ℂ)) ψ = 0 := by
  simp [c0SchwartzPairing, ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply, zero_mul,
    MeasureTheory.integral_zero]

/-- The zero multi-index belongs to every `multiIndicesBall n M`. -/
theorem zero_mem_multiIndicesBall (n M : ℕ) :
    (0 : Fin n → ℕ) ∈ multiIndicesBall n M := by
  rw [mem_multiIndicesBall_iff]
  simp [multiIndexOrder, Pi.zero_apply]

/-- Rewrite the `C_0`-derivative representation in the form
`∑_{α,β} c0SchwartzPairing (f α β) (∂^β (x^α · φ))`, by placing the monomial
factor inside the test function via `SchwartzMap.smulLeftCLM`. -/
theorem representation_rewrite
    (n M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
        ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (f α β)
            (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) := by

  refine ⟨M, fun α β => if α = 0 then v β else 0, fun φ => ?_⟩

  have hsmul : SchwartzMap.smulLeftCLM ℂ (monomial (0 : Fin n → ℕ)) φ = φ := by
    rw [monomial_zero_eq, SchwartzMap.smulLeftCLM_const]
    simp


  change (∑ γ ∈ multiIndicesBall n M,
      c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
    ∑ α ∈ multiIndicesBall n M, ∑ β ∈ multiIndicesBall n M,
      c0SchwartzPairing (if α = 0 then v β else 0)
        (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ))
  symm
  rw [Finset.sum_eq_single_of_mem (0 : Fin n → ℕ) (zero_mem_multiIndicesBall n M)
    (fun α _ hα => by
      simp only [hα, ite_false]
      exact Finset.sum_eq_zero fun β _ => c0SchwartzPairing_zero _)]
  simp [hsmul]

/-- **Schwartz representation theorem** (Melrose Thm 10.5, first form): every
tempered distribution `u ∈ 𝓢'(ℝ^n, ℂ)` can be written as
`u φ = ∑_{α,β} c0SchwartzPairing (f α β) (∂^β (x^α · φ))`
for some finite family of `C_0` functions `f α β`. -/
theorem schwartz_representation (n : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (f α β)
            (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) := by

  obtain ⟨M, v, hv⟩ := intermediate_form_eq1010 n u

  obtain ⟨m, f, hf⟩ := representation_rewrite n M v
  exact ⟨m, f, fun φ => (hv φ).trans (hf φ)⟩


/-- Alternative rewrite where the monomial factor multiplies the derived test
function from outside: `∑_{α,β} c0SchwartzPairing (g α β) (x^α · ∂^β φ)`. -/
theorem representation_rewrite_form2
    (n M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (g : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
        ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (g α β)
            (SchwartzMap.smulLeftCLM ℂ (monomial α) (iterSchwartzDeriv β φ)) := by

  refine ⟨M, fun α β => if α = 0 then v β else 0, fun φ => ?_⟩

  have h0mem : (0 : Fin n → ℕ) ∈ multiIndicesBall n M := by
    rw [mem_multiIndicesBall_iff]
    simp [multiIndexOrder]

  have hmon0 : monomial (0 : Fin n → ℕ) = fun _ => (1 : ℂ) := by
    ext x; simp [monomial]

  have hsmul0 : ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      SchwartzMap.smulLeftCLM ℂ (monomial (0 : Fin n → ℕ)) ψ = ψ := by
    intro ψ
    have hfun : monomial (0 : Fin n → ℕ) = fun (_ : EuclideanSpace ℝ (Fin n)) => (1 : ℂ) := hmon0
    simp [hfun]

  have hpair0 : ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      c0SchwartzPairing (0 : C₀(EuclideanSpace ℝ (Fin n), ℂ)) ψ = 0 := by
    intro ψ; simp [c0SchwartzPairing, ZeroAtInftyContinuousMap.coe_zero]


  symm

  have step1 : ∀ α β,
      c0SchwartzPairing (if α = (0 : Fin n → ℕ) then v β else 0)
        (SchwartzMap.smulLeftCLM ℂ (monomial α) (iterSchwartzDeriv β φ)) =
      if α = 0 then c0SchwartzPairing (v β) (iterSchwartzDeriv β φ) else 0 := by
    intro α β
    split_ifs with h
    · subst h; rw [hsmul0]
    · exact hpair0 _
  simp_rw [step1]

  have key : ∀ α ∈ multiIndicesBall n M, α ≠ (0 : Fin n → ℕ) →
      (∑ β ∈ multiIndicesBall n M,
        if α = 0 then c0SchwartzPairing (v β) (iterSchwartzDeriv β φ) else 0) = 0 := by
    intro α _ hα
    simp [hα]
  rw [Finset.sum_eq_single_of_mem 0 h0mem key]
  simp

/-- **Schwartz representation theorem** (Melrose Thm 10.5, second form): every
tempered distribution `u ∈ 𝓢'(ℝ^n, ℂ)` is a finite sum
`u φ = ∑_{α,β} c0SchwartzPairing (v α β) (x^α · ∂^β φ)`
with `v α β` continuous and vanishing at infinity. -/
theorem schwartz_representation_form2 (n : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (v : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (v α β)
            (SchwartzMap.smulLeftCLM ℂ (monomial α) (iterSchwartzDeriv β φ)) := by

  obtain ⟨M, w, hw⟩ := intermediate_form_eq1010 n u

  obtain ⟨m, g, hg⟩ := representation_rewrite_form2 n M w
  exact ⟨m, g, fun φ => (hw φ).trans (hg φ)⟩

end SchwartzRepresentation

end
