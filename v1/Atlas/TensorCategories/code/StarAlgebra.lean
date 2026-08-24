/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.GrothendieckRing
import Atlas.TensorCategories.code.BasedRings
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 800000

open Finset Complex

/-- A `*`-algebra with trace: an associative ℂ-algebra with a star structure, a linear trace
satisfying `τ(ab) = τ(ba)`, and a positive definiteness condition `0 < Re τ(a * star a)` for
`a ≠ 0`. -/
structure StarAlgWithTrace where
  carrier : Type*
  [instRing : Ring carrier]
  [instAlgebra : Algebra ℂ carrier]
  [instStarRing : StarRing carrier]
  [instStarModule : StarModule ℂ carrier]
  trace : carrier →ₗ[ℂ] ℂ
  trace_comm : ∀ a b, trace (a * b) = trace (b * a)
  trace_pos_def : ∀ a, a ≠ 0 → 0 < (trace (a * star a)).re

attribute [instance] StarAlgWithTrace.instRing StarAlgWithTrace.instAlgebra
  StarAlgWithTrace.instStarRing StarAlgWithTrace.instStarModule

/-- Definition 1.43.1: A `*`-algebra is an associative algebra `B` over `ℂ` with an antilinear
anti-involution and a trace functional whose Hermitian form is positive definite. -/
abbrev Definition_1_43_1 := StarAlgWithTrace

namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

/-- If `a` is nonzero in a `*`-algebra with trace, then `a * star a` is nonzero, since otherwise
the trace `τ(a * star a)` would vanish, contradicting positive definiteness. -/
lemma mul_star_ne_zero (a : B.carrier) (ha : a ≠ 0) : a * star a ≠ 0 := by
  intro h
  have h1 := B.trace_pos_def a ha
  rw [h, map_zero] at h1
  simp at h1

/-- A finite-dimensional ℂ-algebra is Artinian as a ring. -/
instance [FiniteDimensional ℂ B.carrier] : IsArtinianRing B.carrier :=
  isArtinian_of_tower ℂ inferInstance

/-- The element `a * star a` is self-adjoint. -/
lemma star_mul_star_self (a : B.carrier) : star (a * star a) = a * star a := by
  rw [star_mul, star_star]

/-- Powers of a self-adjoint element are again self-adjoint. -/
lemma star_pow_of_star_self {a : B.carrier} (hstar : star a = a) (n : ℕ) :
    star (a ^ n) = a ^ n := by
  rw [star_pow, hstar]

/-- If `a` is a nonzero self-adjoint element of a `*`-algebra with trace, then `a²` is nonzero. -/
lemma sq_ne_zero_of_star_self {a : B.carrier} (ha : a ≠ 0) (hstar : star a = a) :
    a ^ 2 ≠ 0 := by
  rw [sq, show a * a = a * star a from by rw [hstar]]
  exact B.mul_star_ne_zero a ha

/-- The Jacobson radical of a finite-dimensional `*`-algebra with trace vanishes; this is the
key step en route to semisimplicity, using nilpotency of the Jacobson radical together with the
positive-definiteness of the trace. -/
theorem jacobson_eq_bot [FiniteDimensional ℂ B.carrier] : Ring.jacobson B.carrier = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  by_contra h
  set J := Ring.jacobson B.carrier with hJ_def

  have hJ_nilp := IsArtinianRing.isNilpotent_jacobson_bot (R := B.carrier)
  rw [Ideal.jacobson_bot] at hJ_nilp
  obtain ⟨n, hn⟩ := hJ_nilp

  set c := a * star a with hc_def
  have hc_mem : c ∈ J := J.mul_mem_right (star a) ha
  have hc_ne : c ≠ 0 := B.mul_star_ne_zero a h
  have hc_star : star c = c := B.star_mul_star_self a

  have key : ∀ k : ℕ, c ^ (2 ^ k) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hc_ne
    | succ k ih =>

      rw [pow_succ, pow_mul]
      exact B.sq_ne_zero_of_star_self ih (B.star_pow_of_star_self hc_star _)

  have hmem : c ^ (2 ^ n) ∈ J ^ (2 ^ n) := Ideal.pow_mem_pow hc_mem _
  have hzero : J ^ (2 ^ n) = ⊥ := by
    rw [eq_bot_iff]
    exact (Ideal.pow_le_pow_right Nat.lt_two_pow_self.le).trans (le_of_eq hn)
  rw [hzero] at hmem
  exact key n ((Submodule.mem_bot _).mp hmem)

/-- Any finite-dimensional `*`-algebra with trace is semisimple as a ring. -/
theorem starAlgWithTrace_isSemisimple [FiniteDimensional ℂ B.carrier] :
    @IsSemisimpleRing B.carrier B.instRing := by
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson]
  exact B.jacobson_eq_bot

end StarAlgWithTrace

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The duality map `star : ι → ι` packaged as an `Equiv` using its involutivity. -/
def starEquivC : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- The complex-coefficient multiplication on the Grothendieck ring of a fusion ring,
expanded against the structure constants `N i j k`. -/
def grMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- The complex-coefficient star on `ι → ℂ`: complex-conjugate the coefficient and dualise the
index via `R.star`. -/
def grStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace on `ι → ℂ`: take the coefficient at the unit basis vector. -/
def grTraceC (f : ι → ℂ) : ℂ := f R.unit

/-- The trace on the complexified Grothendieck ring is symmetric: `τ(ab) = τ(ba)`. -/
theorem trace_comm_grC (a b : ι → ℂ) :
    R.grTraceC (R.grMulC a b) = R.grTraceC (R.grMulC b a) := by
  unfold grTraceC grMulC
  simp_rw [R.duality, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

  rw [← Equiv.sum_comp R.starEquivC (fun x => a x * b (R.star x))]
  simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

/-- The pairing `τ(a * star a)` equals the sum of squared norms of the coefficients of `a`. -/
theorem trace_star_mul_eq_sum_normSq (a : ι → ℂ) :
    R.grTraceC (R.grMulC a (R.grStarC a)) =
      ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
  unfold grTraceC grMulC grStarC
  simp_rw [R.duality, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true, R.star_star]
  congr 1; ext i; rw [mul_conj]

/-- The real part of `τ(a * star a)` equals the sum of squared norms of the coefficients. -/
theorem trace_star_mul_re (a : ι → ℂ) :
    (R.grTraceC (R.grMulC a (R.grStarC a))).re =
      ∑ i : ι, Complex.normSq (a i) := by
  rw [trace_star_mul_eq_sum_normSq]
  simp [Complex.ofReal_re]

/-- Positive definiteness of the Hermitian trace form on the complexified Grothendieck ring of a
fusion ring. -/
theorem trace_pos_def_grC (a : ι → ℂ) (ha : a ≠ 0) :
    0 < (R.grTraceC (R.grMulC a (R.grStarC a))).re := by
  rw [trace_star_mul_re]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- Fusion-ring version of Proposition 1.43.4: the complexification of a based fusion ring
carries a canonical `*`-algebra structure with star involutive, trace symmetric, and Hermitian
form positive definite. -/
theorem Proposition_1_43_4_fusion :

    (∀ f : ι → ℂ, R.grStarC (R.grStarC f) = f) ∧

    (∀ a b : ι → ℂ, R.grTraceC (R.grMulC a b) = R.grTraceC (R.grMulC b a)) ∧

    (∀ a : ι → ℂ, a ≠ 0 → 0 < (R.grTraceC (R.grMulC a (R.grStarC a))).re) := by
  exact ⟨by
    intro f; ext i; simp [grStarC, R.star_star],
    R.trace_comm_grC,
    R.trace_pos_def_grC⟩

end

end FusionRing

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The duality map on indices of a multifusion ring, packaged as an `Equiv`. -/
def starEquivC' : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- Multiplication on the complexified multifusion ring, expanded against structure constants. -/
def grMulC' (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- The star map on the complexified multifusion ring: conjugate the coefficient and dualise
the index. -/
def grStarC' (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace on the complexified multifusion ring: sum coefficients over the indecomposable
units `I₀`. -/
def grTraceC' (f : ι → ℂ) : ℂ :=
  ∑ k ∈ R.I₀, f k

/-- The star operation on the complexified multifusion ring is involutive. -/
theorem grStarC'_invol (f : ι → ℂ) : R.grStarC' (R.grStarC' f) = f := by
  ext i; simp [grStarC', R.star_star]

/-- The star operation on the complexified multifusion ring is an anti-homomorphism:
`star(fg) = star(g) star(f)`. -/
theorem grStarC'_anti_mul (f g : ι → ℂ) :
    R.grStarC' (R.grMulC' f g) = R.grMulC' (R.grStarC' g) (R.grStarC' f) := by
  ext k
  simp only [grStarC', grMulC']
  rw [map_sum]
  simp_rw [map_sum, map_mul, starRingEnd_apply, star_natCast]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [R.star_anti i j (R.star k), R.star_star k]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j
    rw [← Equiv.sum_comp R.starEquivC']
  rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  congr 1; ext i; congr 1; ext j; ring

/-- For multifusion rings: `τ(a * star a)` equals the sum of squared norms of the coefficients
of `a`. -/
theorem trace_star_mul_eq_sum_normSq' (a : ι → ℂ) :
    R.grTraceC' (R.grMulC' a (R.grStarC' a)) =
      ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
  simp only [grTraceC', grMulC', grStarC']
  simp_rw [Finset.sum_comm (s := R.I₀)]
  simp_rw [← Finset.mul_sum]
  have cast_sum : ∀ i j, (∑ k ∈ R.I₀, (R.N i j k : ℂ)) =
      ((∑ k ∈ R.I₀, R.N i j k : ℕ) : ℂ) := by
    intros; push_cast; rfl
  simp_rw [cast_sum, R.duality_trace, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
           mul_ite, mul_one, mul_zero]
  conv_lhs =>
    arg 2; ext i
    rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  simp_rw [sum_ite_eq, mem_univ, if_true]
  congr 1; ext i; rw [mul_conj]

/-- The real part of the trace pairing equals the sum of squared norms for multifusion rings. -/
theorem trace_star_mul_re' (a : ι → ℂ) :
    (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re =
      ∑ i : ι, Complex.normSq (a i) := by
  rw [trace_star_mul_eq_sum_normSq']
  simp [Complex.ofReal_re]

/-- For multifusion rings: the trace is symmetric, `τ(ab) = τ(ba)`. -/
theorem trace_comm_grC' (a b : ι → ℂ) :
    R.grTraceC' (R.grMulC' a b) = R.grTraceC' (R.grMulC' b a) := by
  simp only [grTraceC', grMulC']
  simp_rw [Finset.sum_comm (s := R.I₀)]
  simp_rw [← Finset.mul_sum]
  have cast_sum : ∀ i j, (∑ k ∈ R.I₀, (R.N i j k : ℂ)) =
      ((∑ k ∈ R.I₀, R.N i j k : ℕ) : ℂ) := by
    intros; push_cast; rfl
  simp_rw [cast_sum, R.duality_trace, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
           mul_ite, mul_one, mul_zero]
  conv_lhs =>
    arg 2; ext i
    rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  simp_rw [sum_ite_eq, mem_univ, if_true]
  conv_rhs =>
    arg 2; ext i
    rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  simp_rw [sum_ite_eq, mem_univ, if_true]
  rw [← Equiv.sum_comp R.starEquivC']
  simp only [starEquivC', Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

/-- For multifusion rings: the Hermitian trace form is positive definite. -/
theorem trace_pos_def_grC' (a : ι → ℂ) (ha : a ≠ 0) :
    0 < (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re := by
  rw [trace_star_mul_re']
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- Proposition 1.43.4: the complexification of a (multifusion) based ring is canonically a
`*`-algebra: star is involutive, anti-multiplicative, the trace is symmetric, and the Hermitian
form is positive definite. -/
theorem Proposition_1_43_4 :

    (∀ f : ι → ℂ, R.grStarC' (R.grStarC' f) = f) ∧

    (∀ f g : ι → ℂ, R.grStarC' (R.grMulC' f g) = R.grMulC' (R.grStarC' g) (R.grStarC' f)) ∧

    (∀ a b : ι → ℂ, R.grTraceC' (R.grMulC' a b) = R.grTraceC' (R.grMulC' b a)) ∧

    (∀ a : ι → ℂ, a ≠ 0 → 0 < (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re) :=
  ⟨R.grStarC'_invol, R.grStarC'_anti_mul, R.trace_comm_grC', R.trace_pos_def_grC'⟩

end

end MultifusionRingDef
