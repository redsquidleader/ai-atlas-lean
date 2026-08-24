/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.StarAlgebra
import Atlas.TensorCategories.code.BasedRings
import Atlas.TensorCategories.code.MfStarAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-- Proposition 1.43.2 (lowercase alias): every finite-dimensional `*`-algebra with trace is
semisimple. -/
theorem prop_1_43_2 (B : StarAlgWithTrace) [FiniteDimensional ℂ B.carrier] :
    @IsSemisimpleRing B.carrier B.instRing :=
  B.starAlgWithTrace_isSemisimple

/-- Proposition 1.43.2: any finite-dimensional `*`-algebra is semisimple. -/
theorem Proposition_1_43_2 (B : StarAlgWithTrace) [FiniteDimensional ℂ B.carrier] :
    @IsSemisimpleRing B.carrier B.instRing :=
  B.starAlgWithTrace_isSemisimple

set_option maxHeartbeats 400000

open Finset Complex

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The star map of a multifusion ring packaged as an `Equiv`. -/
def starEquivC : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- Multiplication on the complexified multifusion ring, expanded against structure constants. -/
def grMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- The star operation on the complexified multifusion ring. -/
def grStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace functional on the complexified multifusion ring, summing over the indecomposable
units in `I₀`. -/
def grTraceC (f : ι → ℂ) : ℂ :=
  ∑ k ∈ R.I₀, f k

/-- Complex-valued duality identity: `∑_{k ∈ I₀} N i j k = if i = star j then 1 else 0`. -/
lemma duality_trace_cast (i j : ι) :
    (∑ k ∈ R.I₀, (R.N i j k : ℂ)) = if i = R.star j then 1 else 0 := by
  have h := R.duality_trace i j
  have : (∑ k ∈ R.I₀, (R.N i j k : ℂ)) = ((∑ k ∈ R.I₀, R.N i j k : ℕ) : ℂ) := by
    push_cast; rfl
  rw [this, h]; split_ifs <;> simp

/-- Pairing formula: `τ(fg) = ∑_j f(star j) * g(j)`. -/
lemma trace_mul_eq (f g : ι → ℂ) :
    R.grTraceC (R.grMulC f g) = ∑ j : ι, f (R.star j) * g j := by
  unfold grTraceC grMulC
  rw [Finset.sum_comm (s := R.I₀)]
  simp_rw [Finset.sum_comm (s := R.I₀) (t := univ)]
  simp_rw [← Finset.mul_sum, duality_trace_cast]
  simp_rw [show ∀ i j : ι, (i = R.star j) ↔ (j = R.star i) from
    fun i j => ⟨fun h => by rw [h, R.star_star], fun h => by rw [h, R.star_star]⟩]
  simp_rw [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [← Equiv.sum_comp R.starEquivC]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]

/-- Symmetry of the trace on the complexified multifusion ring: `τ(ab) = τ(ba)`. -/
theorem trace_comm_based (a b : ι → ℂ) :
    R.grTraceC (R.grMulC a b) = R.grTraceC (R.grMulC b a) := by
  rw [trace_mul_eq, trace_mul_eq]
  rw [← Equiv.sum_comp R.starEquivC (fun j => a (R.star j) * b j)]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

/-- The pairing `τ(a * star a)` equals the sum of squared norms of the coefficients of `a`. -/
theorem trace_star_mul_eq_sum_normSq (a : ι → ℂ) :
    R.grTraceC (R.grMulC a (R.grStarC a)) =
      ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
  rw [trace_mul_eq]
  simp only [grStarC]
  simp_rw [mul_conj]
  rw [← Equiv.sum_comp R.starEquivC (fun j => (Complex.normSq (a j) : ℂ))]
  simp only [starEquivC, Equiv.coe_fn_mk]

/-- The real part of `τ(a * star a)` equals the sum of squared norms of the coefficients. -/
theorem trace_star_mul_re (a : ι → ℂ) :
    (R.grTraceC (R.grMulC a (R.grStarC a))).re =
      ∑ i : ι, Complex.normSq (a i) := by
  rw [trace_star_mul_eq_sum_normSq]
  simp [Complex.ofReal_re]

/-- Positive definiteness of the Hermitian trace form on the complexified based ring. -/
theorem trace_pos_def_based (a : ι → ℂ) (ha : a ≠ 0) :
    0 < (R.grTraceC (R.grMulC a (R.grStarC a))).re := by
  rw [trace_star_mul_re]
  apply Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (a i))
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- The star operation on the complexified multifusion ring is involutive. -/
theorem grStarC_involution (f : ι → ℂ) :
    R.grStarC (R.grStarC f) = f := by
  ext i
  simp [grStarC, R.star_star]

/-- The star operation on the complexified multifusion ring is an anti-homomorphism. -/
theorem grStarC_anti_mul (f g : ι → ℂ) :
    R.grStarC (R.grMulC f g) = R.grMulC (R.grStarC g) (R.grStarC f) := by
  ext k
  simp only [grStarC, grMulC]
  simp_rw [map_sum, map_mul, map_natCast]


  simp_rw [show ∀ i j, (R.N i j (R.star k) : ℂ) = (R.N (R.star j) (R.star i) k : ℂ)
    from fun i j => by congr 1; rw [R.star_anti]; congr 1; exact (R.star_star k)]


  rw [Finset.sum_comm]


  conv_lhs => rw [← Equiv.sum_comp R.starEquivC]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]


  congr 1; ext j
  conv_lhs => rw [← Equiv.sum_comp R.starEquivC]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]


  congr 1; ext i; ring

/-- Proposition 1.43.4: the complexified multifusion ring `R ⊗_ℤ ℂ` is canonically a
`*`-algebra with trace, packaged as a term of `StarAlgWithTrace`. -/
noncomputable def prop_1_43_4 : StarAlgWithTrace :=
  R.mfGrStarAlgWithTrace

end

end MultifusionRingDef
