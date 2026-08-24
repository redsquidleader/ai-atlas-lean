/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.StarAlgebra
import Atlas.TensorCategories.code.FrobeniusPerron
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

/-- Corollary 1.43.3: a nonzero idempotent in a finite-dimensional `*`-algebra with trace has
positive real trace. -/
theorem trace_pos_of_idempotent (e : B.carrier) (he_idem : e * e = e)
    (he_ne : e ≠ 0) : 0 < (B.trace e).re := by sorry

/-- If `1 ≠ 0` in a `*`-algebra with trace, then the trace of `1` is positive. -/
theorem trace_one_pos (hne : (1 : B.carrier) ≠ 0) : 0 < (B.trace 1).re :=
  B.trace_pos_of_idempotent 1 (mul_one 1) hne

end StarAlgWithTrace

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

noncomputable section

/-- The complex basis vector concentrated at index `i`. -/
def basisVecC (i : ι) : ι → ℂ :=
  fun k => if k = i then 1 else 0

/-- The star operation sends the basis vector at `i` to the basis vector at `star i`. -/
theorem grStarC_basisVecC (i : ι) :
    R.grStarC (basisVecC i) = basisVecC (R.star i) := by
  funext j
  unfold grStarC basisVecC
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero]
  congr 1
  exact propext ⟨fun h => by rw [← h, R.star_star], fun h => by rw [h, R.star_star]⟩

omit [Fintype ι] in
/-- The basis vector `basisVecC i` is nonzero. -/
theorem basisVecC_ne_zero (i : ι) : basisVecC i ≠ (0 : ι → ℂ) := by
  intro h
  have : (basisVecC i : ι → ℂ) i = (0 : ι → ℂ) i := congrFun h i
  unfold basisVecC at this
  simp at this

/-- The product of two basis vectors at indices `i, j` evaluated at `k` recovers the structure
constant `N i j k`. -/
theorem grMulC_basisVecC_eq (i j k : ι) :
    R.grMulC (basisVecC i) (basisVecC j) k = (R.N i j k : ℂ) := by
  unfold grMulC basisVecC
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true]

/-- The trace of the product of two basis vectors equals the structure constant `N i j unit`. -/
theorem grTraceC_basisVecC_mul (i j : ι) :
    R.grTraceC (R.grMulC (basisVecC i) (basisVecC j)) = (R.N i j R.unit : ℂ) := by
  unfold grTraceC
  exact R.grMulC_basisVecC_eq i j R.unit

/-- In a fusion ring, the multiplicity of the unit in `i * star i` is exactly 1 (duality). -/
theorem N_self_star_unit (i : ι) : R.N i (R.star i) R.unit = 1 := by
  rw [R.duality]; simp

/-- The trace pairing of `basisVecC i` with its dual `basisVecC (star i)` equals 1. -/
theorem grMulC_basisVecC_dual_trace (i : ι) :
    R.grTraceC (R.grMulC (basisVecC i) (basisVecC (R.star i))) = 1 := by
  rw [R.grTraceC_basisVecC_mul, R.N_self_star_unit]; simp

/-- The trace of a basis vector is `1` if the index equals the unit, and `0` otherwise. -/
theorem grTraceC_basisVecC_val (i : ι) :
    R.grTraceC (basisVecC i) = if i = R.unit then 1 else 0 := by
  unfold grTraceC basisVecC
  by_cases h : R.unit = i
  · simp [h]
  · simp [h, Ne.symm h]

/-- The trace of the unit basis vector is `1`. -/
theorem grTraceC_basisVecC_unit :
    R.grTraceC (basisVecC R.unit) = 1 := by
  rw [grTraceC_basisVecC_val]; simp

/-- Iterated multiplication of `f : ι → ℂ` with itself in the complexified Grothendieck ring,
starting from the multiplicative unit at exponent 0. -/
def grPowC (R : FusionRing ι) (f : ι → ℂ) : ℕ → (ι → ℂ)
  | 0 => fun k => if k = R.unit then 1 else 0
  | n + 1 => R.grMulC (grPowC R f n) f

/-- The zeroth power `grPowC R f 0` is the multiplicative identity. -/
theorem grPowC_zero (f : ι → ℂ) (k : ι) :
    grPowC R f 0 k = if k = R.unit then 1 else 0 := rfl

/-- Definitional unfolding of `grPowC` at a successor exponent. -/
theorem grPowC_succ (f : ι → ℂ) (n : ℕ) :
    grPowC R f (n + 1) = R.grMulC (grPowC R f n) f := rfl

/-- Left multiplicative identity for `grMulC`. -/
theorem grMulC_one_left (f : ι → ℂ) :
    R.grMulC (fun k => if k = R.unit then 1 else 0) f = f := by
  funext k; unfold grMulC
  simp_rw [ite_mul, one_mul, zero_mul]
  conv_lhs => arg 2; ext i; rw [show (∑ j, (if i = R.unit then f j * (R.N i j k : ℂ)
    else 0)) = if i = R.unit then ∑ j, f j * (R.N i j k : ℂ) else 0
    from by split <;> simp_all]
  simp_rw [sum_ite_eq', mem_univ, if_true]
  simp_rw [R.unit_mul, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

/-- `grPowC R f 1 = f`. -/
theorem grPowC_one (f : ι → ℂ) : grPowC R f 1 = f := by
  show R.grMulC (fun k => if k = R.unit then 1 else 0) f = f
  exact R.grMulC_one_left f

/-- For the unit basis vector there is some positive power whose trace has positive real part
(taking `n = 1` works). -/
theorem exists_pos_trace_power_unit :
    ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC R.unit) n)).re := by
  refine ⟨1, Nat.one_pos, ?_⟩
  rw [grPowC_one]
  rw [R.grTraceC_basisVecC_unit]
  norm_num

/-- For a self-dual basis vector (i.e. `star i = i`), `n = 2` gives a power with positive real
trace. -/
theorem exists_pos_trace_power_selfdual (i : ι) (hsd : R.star i = i) :
    ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC i) n)).re := by
  refine ⟨2, by omega, ?_⟩
  show 0 < (R.grTraceC (R.grMulC (R.grMulC (fun k => if k = R.unit then 1 else 0)
    (basisVecC i)) (basisVecC i))).re
  rw [R.grMulC_one_left]
  rw [R.grTraceC_basisVecC_mul, R.duality, hsd, if_pos rfl]
  norm_num

/-- The trace pairing of a basis vector with its dual basis vector has positive real part. -/
theorem trace_basis_product_pos (i : ι) :
    0 < (R.grTraceC (R.grMulC (basisVecC i) (basisVecC (R.star i)))).re := by
  rw [R.grTraceC_basisVecC_mul, R.N_self_star_unit]
  norm_num

/-- For the unit or any self-dual basis element, some positive power has positive real trace. -/
theorem exists_pos_trace_power (i : ι) (hi : i = R.unit ∨ R.star i = i) :
    ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC i) n)).re := by
  rcases hi with rfl | hsd
  · exact R.exists_pos_trace_power_unit
  · exact R.exists_pos_trace_power_selfdual i hsd

/-- Reduction step: the trace of `(basisVecC i)^(n+1)` equals the coefficient at index `star i`
of `(basisVecC i)^n`. -/
lemma grTraceC_grPowC_succ (i : ι) (n : ℕ) :
    R.grTraceC (grPowC R (basisVecC i) (n + 1)) =
    grPowC R (basisVecC i) n (R.star i) := by
  unfold grTraceC
  show (R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)) R.unit = _
  unfold grMulC basisVecC
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [R.duality]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
  conv_lhs =>
    arg 2; ext j
    rw [show (if i = R.star j then grPowC R (fun k => if k = i then 1 else 0) n j
            else 0) =
          (if j = R.star i then grPowC R (fun k => if k = i then 1 else 0) n j
            else 0)
      from by
        congr 1
        exact propext ⟨fun h => by rw [← R.star_star j, h],
                       fun h => by rw [h, R.star_star]⟩]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Every coefficient of a power of a basis vector is a non-negative integer (a structure
constant), hence equals some natural number cast to `ℂ`. -/
lemma grPowC_basisVecC_nonneg (i : ι) (n : ℕ) (k : ι) :
    ∃ m : ℕ, grPowC R (basisVecC i) n k = (m : ℂ) := by
  induction n generalizing k with
  | zero =>
    use if k = R.unit then 1 else 0
    simp only [grPowC]
    split <;> simp
  | succ n ih =>
    show ∃ m : ℕ, (R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)) k = ↑m
    unfold grMulC basisVecC
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

    suffices ∃ m : ℕ, ∑ j : ι, grPowC R (fun l => if l = i then 1 else 0) n j *
        (R.N j i k : ℂ) = (m : ℂ) by exact this

    have : ∀ j, ∃ mj : ℕ, grPowC R (fun l => if l = i then 1 else 0) n j *
        (R.N j i k : ℂ) = (mj : ℂ) := by
      intro j
      obtain ⟨c, hc⟩ := ih j
      exact ⟨c * R.N j i k, by push_cast; unfold basisVecC at hc; rw [hc]⟩
    choose mj hmj using this
    exact ⟨∑ j : ι, mj j, by push_cast; exact Finset.sum_congr rfl (fun j _ => hmj j)⟩

/-- If some coefficient of `(basisVecC i)^n` has positive real part, then so does some
coefficient of `(basisVecC i)^(n+1)`. -/
lemma grPowC_basisVecC_succ_ne_zero (i : ι) (n : ℕ)
    (hn : ∃ k : ι, 0 < (grPowC R (basisVecC i) n k).re) :
    ∃ k : ι, 0 < (grPowC R (basisVecC i) (n + 1) k).re := by
  obtain ⟨j, hj⟩ := hn

  obtain ⟨m, _, hm⟩ := Finset.exists_lt_of_sum_lt
    (show ∑ _k : ι, (0 : ℕ) < ∑ k : ι, R.N j i k by
      simp only [Finset.sum_const_zero]; exact R.sum_N_pos j i)

  use m
  show 0 < ((R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)) m).re
  unfold grMulC basisVecC
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_im, mul_zero, sub_zero,
    Complex.natCast_re, Complex.re_ofNat]

  apply lt_of_lt_of_le _ (Finset.sum_le_sum (fun l _ => le_refl _))
  apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun l => (grPowC R (fun k => if k = i then (1 : ℂ) else 0) n l).re * (R.N l i m : ℝ)) (fun l _ => ?_) (Finset.mem_univ j))
  · apply mul_pos hj
    exact Nat.cast_pos.mpr (by omega)
  ·
    apply mul_nonneg
    · obtain ⟨c, hc⟩ := R.grPowC_basisVecC_nonneg i n l
      unfold basisVecC at hc
      rw [hc]; simp [Nat.cast_nonneg]
    · exact Nat.cast_nonneg _

/-- For every positive `n`, some coefficient of `(basisVecC i)^n` has positive real part. -/
lemma grPowC_basisVecC_ne_zero (i : ι) (n : ℕ) (hn : 0 < n) :
    ∃ k : ι, 0 < (grPowC R (basisVecC i) n k).re := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>

      use i
      rw [R.grPowC_one]
      unfold basisVecC
      simp
    | succ m =>
      exact R.grPowC_basisVecC_succ_ne_zero i (m + 1) (ih (by omega))

/-- Pulling a constant `if` condition out of a sum. -/
lemma sum_ite_const_zeroC {α : Type*} [AddCommMonoid α] {ι' : Type*}
    {p : Prop} [Decidable p] (s : Finset ι') (f : ι' → α) :
    (∑ x ∈ s, if p then f x else 0) = if p then ∑ x ∈ s, f x else 0 := by
  split <;> simp_all

/-- Complex-valued associativity of the fusion structure constants. -/
lemma assoc_complex (i j k l : ι) :
    (univ.sum fun m => (R.N i j m : ℂ) * (R.N m k l : ℂ)) =
    (univ.sum fun m => (R.N j k m : ℂ) * (R.N i m l : ℂ)) := by
  exact_mod_cast R.assoc i j k l

/-- Complex-valued unit-multiplication: `(N unit j k : ℂ) = 1` if `j = k` else `0`. -/
lemma unit_mul_complex (j k : ι) :
    (R.N R.unit j k : ℂ) = if j = k then 1 else 0 := by
  rw [R.unit_mul]; split <;> simp

/-- Complex-valued unit-multiplication on the right: `(N i unit k : ℂ) = 1` if `i = k`. -/
lemma mul_unit_complex (i k : ι) :
    (R.N i R.unit k : ℂ) = if i = k then 1 else 0 := by
  rw [R.mul_unit]; split <;> simp

/-- Right multiplicative identity for `grMulC`. -/
theorem grMulC_one_right (f : ι → ℂ) :
    R.grMulC f (fun k => if k = R.unit then 1 else 0) = f := by
  funext k; unfold grMulC
  simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true, R.mul_unit_complex,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

/-- Associativity-shifted reindexing of an inner sum used in `grMulC_assoc`. -/
lemma inner_sum_eqC (a b c : ι → ℂ) (l i j k : ι) :
    (∑ m : ι, a i * (b j * (c k * ((R.N i j m : ℂ) * (R.N m k l : ℂ))))) =
    (∑ q : ι, a i * (b j * (c k * ((R.N j k q : ℂ) * (R.N i q l : ℂ))))) := by
  simp_rw [← Finset.mul_sum]
  congr 3
  exact R.assoc_complex i j k l

/-- Associativity of `grMulC`. -/
theorem grMulC_assoc (a b c : ι → ℂ) :
    R.grMulC (R.grMulC a b) c = R.grMulC a (R.grMulC b c) := by
  funext l; simp only [grMulC]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  trans (∑ i : ι, ∑ j, ∑ k, ∑ m,
    a i * (b j * (c k * ((R.N i j m : ℂ) * (R.N m k l : ℂ)))))
  · rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k; congr 1; ext m; ring
  · conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k
    exact R.inner_sum_eqC a b c l i j k

/-- Left distributivity of `grMulC` over pointwise addition. -/
theorem grMulC_left_distrib (a b c : ι → ℂ) :
    R.grMulC a (fun k => b k + c k) = fun k => R.grMulC a b k + R.grMulC a c k := by
  funext l; simp only [grMulC]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

/-- Right distributivity of `grMulC` over pointwise addition. -/
theorem grMulC_right_distrib (a b c : ι → ℂ) :
    R.grMulC (fun k => a k + b k) c = fun k => R.grMulC a c k + R.grMulC b c k := by
  funext l; simp only [grMulC]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- `grMulC` with the zero function on the right yields zero. -/
theorem grMulC_zero (a : ι → ℂ) :
    R.grMulC a (fun _ => 0) = fun _ => 0 := by
  funext l; simp only [grMulC]; simp

/-- `grMulC` with the zero function on the left yields zero. -/
theorem grZeroC_mul (a : ι → ℂ) :
    R.grMulC (fun _ => 0) a = fun _ => 0 := by
  funext l; simp only [grMulC]; simp

/-- Pulling a scalar from the first argument through `grMulC`. -/
theorem grMulC_smul_left (c : ℂ) (a b : ι → ℂ) :
    R.grMulC (fun k => c * a k) b = fun k => c * R.grMulC a b k := by
  funext l; simp only [grMulC]
  simp_rw [mul_assoc, Finset.mul_sum]

/-- Cyclic identity for the structure constants: `N i j (star k) = N j k (star i)`. -/
lemma N_cyclic (i j k : ι) :
    R.N i j (R.star k) = R.N j k (R.star i) := by


  have h := R.assoc i j k R.unit
  simp only [R.duality] at h
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h


  have : ∀ x : ι, (k = R.star x) = (x = R.star k) :=
    fun x => propext ⟨fun h => by rw [← R.star_star x, h], fun h => by rw [h, R.star_star]⟩
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

/-- Star-reversed structure constants: `N (star j) (star i) k = N i j (star k)`. -/
lemma N_star_reverse (i j k : ι) :
    R.N (R.star j) (R.star i) k = R.N i j (R.star k) := by


  rw [R.N_star_transpose (R.star j) (R.star i) k, R.star_star]

  rw [R.N_cyclic i j k]

/-- Multiplying by a scalar multiple of the unit on the left equals scalar multiplication of
the product by the unit. -/
theorem grMulC_scalar_left (c : ℂ) (f : ι → ℂ) :
    R.grMulC (fun k => if k = R.unit then c else 0) f =
    fun k => c * R.grMulC (fun k => if k = R.unit then 1 else 0) f k := by
  funext l; unfold grMulC
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

/-- Multiplying by a scalar multiple of the unit on the right equals scalar multiplication of
the product by the unit. -/
theorem grMulC_scalar_right (c : ℂ) (f : ι → ℂ) :
    R.grMulC f (fun k => if k = R.unit then c else 0) =
    fun k => c * R.grMulC f (fun k => if k = R.unit then 1 else 0) k := by
  funext l; unfold grMulC
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

/-- The complexified Grothendieck ring of a fusion ring, wrapped as a structure with a single
`coeff : ι → ℂ` field. -/
@[ext]
structure GrRingOfC (R : FusionRing ι) where
  coeff : ι → ℂ

namespace GrRingOfC

variable {R : FusionRing ι}

/-- The zero element of `GrRingOfC R` has all coefficients equal to zero. -/
instance instZero : Zero (GrRingOfC R) := ⟨⟨fun _ => 0⟩⟩
/-- The unit element of `GrRingOfC R` is the indicator function of the multiplicative unit. -/
instance instOne : One (GrRingOfC R) := ⟨⟨fun k => if k = R.unit then 1 else 0⟩⟩

/-- Pointwise addition on `GrRingOfC R`. -/
instance instAdd : Add (GrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Pointwise negation on `GrRingOfC R`. -/
instance instNeg : Neg (GrRingOfC R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Pointwise subtraction on `GrRingOfC R`. -/
instance instSub : Sub (GrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Multiplication on `GrRingOfC R` given by the structure constants `R.N`. -/
instance instMul : Mul (GrRingOfC R) := ⟨fun a b => ⟨R.grMulC a.coeff b.coeff⟩⟩

/-- Pointwise natural-number scalar multiplication on `GrRingOfC R`. -/
instance instSMulNat : SMul ℕ (GrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Pointwise integer scalar multiplication on `GrRingOfC R`. -/
instance instSMulInt : SMul ℤ (GrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- The natural-number cast in `GrRingOfC R` lives entirely at the unit index. -/
instance instNatCast : NatCast (GrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩⟩
/-- The integer cast in `GrRingOfC R` lives entirely at the unit index. -/
instance instIntCast : IntCast (GrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩⟩

/-- Definitional unfolding of the zero coefficient. -/
@[simp] lemma coeff_zero (k : ι) : (0 : GrRingOfC R).coeff k = 0 := rfl
/-- Definitional unfolding of the unit's coefficients. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : GrRingOfC R).coeff k = if k = R.unit then 1 else 0 := rfl
/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : GrRingOfC R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Coefficients commute with negation. -/
@[simp] lemma coeff_neg (a : GrRingOfC R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : GrRingOfC R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- The complexified Grothendieck ring of a fusion ring is a ring. -/
instance instRing : Ring (GrRingOfC R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.grMulC (R.grMulC a.coeff b.coeff) c.coeff) k =
         (R.grMulC a.coeff (R.grMulC b.coeff c.coeff)) k
    rw [R.grMulC_assoc]
  one_mul a := by
    ext k
    show (R.grMulC (fun k => if k = R.unit then 1 else 0) a.coeff) k = a.coeff k
    rw [R.grMulC_one_left]
  mul_one a := by
    ext k
    show (R.grMulC a.coeff (fun k => if k = R.unit then 1 else 0)) k = a.coeff k
    rw [R.grMulC_one_right]
  left_distrib a b c := by
    ext k
    show (R.grMulC a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.grMulC a.coeff b.coeff) k + (R.grMulC a.coeff c.coeff) k
    rw [R.grMulC_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.grMulC (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.grMulC a.coeff c.coeff) k + (R.grMulC b.coeff c.coeff) k
    rw [R.grMulC_right_distrib]
  zero_mul a := by
    ext k
    show (R.grMulC (fun _ => 0) a.coeff) k = 0
    rw [R.grZeroC_mul]
  mul_zero a := by
    ext k
    show (R.grMulC a.coeff (fun _ => 0)) k = 0
    rw [R.grMulC_zero]
  neg_add_cancel a := by ext k; simp
  sub_eq_add_neg a b := by ext k; simp [sub_eq_add_neg]
  zsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  zsmul_zero' a := by ext k; simp
  zsmul_succ' n a := by ext k; simp [add_mul, add_comm]
  zsmul_neg' n a := by
    ext k
    show Int.negSucc n • a.coeff k = -((↑(n + 1) : ℤ) • a.coeff k)
    simp [Int.negSucc_eq, Nat.cast_succ]
    ring
  natCast := fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩
  natCast_zero := by ext k; simp
  natCast_succ m := by
    ext k; show (if k = R.unit then (↑(m + 1) : ℂ) else 0) =
      (if k = R.unit then (m : ℂ) else 0) + (if k = R.unit then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k = R.unit then (m : ℂ) else 0⟩
  intCast_ofNat m := by
    ext k
    show (if k = R.unit then (Int.ofNat m : ℂ) else 0) =
         (if k = R.unit then (m : ℂ) else 0)
    simp [Int.cast_natCast]
  intCast_negSucc m := by
    ext k
    show (if k = R.unit then (Int.negSucc m : ℂ) else 0) =
         -(if k = R.unit then ((m + 1 : ℕ) : ℂ) else 0)
    split
    · simp [Int.negSucc_eq]
    · simp

/-- The ring homomorphism `ℂ →+* GrRingOfC R` sending a scalar `c` to the element supported
at the unit with coefficient `c`. -/
def algebraMapRingHom : ℂ →+* GrRingOfC R where
  toFun c := ⟨fun k => if k = R.unit then c else 0⟩
  map_one' := by ext k; simp
  map_mul' x y := by
    ext k
    change (if k = R.unit then x * y else 0) =
         (R.grMulC (fun k => if k = R.unit then x else 0)
                   (fun k => if k = R.unit then y else 0)) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left]
    split <;> simp_all
  map_zero' := by ext k; simp
  map_add' x y := by
    ext k; change (if k = R.unit then x + y else 0) =
         (if k = R.unit then x else 0) + (if k = R.unit then y else 0)
    split <;> simp

/-- `GrRingOfC R` is a ℂ-algebra via the canonical inclusion `c ↦ c * 1`. -/
instance instAlgebra : Algebra ℂ (GrRingOfC R) where
  smul c a := ⟨fun k => c * a.coeff k⟩
  algebraMap := algebraMapRingHom
  commutes' c a := by
    ext k
    change (R.grMulC (fun k => if k = R.unit then c else 0) a.coeff) k =
         (R.grMulC a.coeff (fun k => if k = R.unit then c else 0)) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left,
        R.grMulC_scalar_right, R.grMulC_one_right]
  smul_def' c a := by
    ext k
    change c * a.coeff k =
         (R.grMulC (fun k => if k = R.unit then c else 0) a.coeff) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left]

/-- The star-ring structure on `GrRingOfC R` defined via the index-dualising involution
`grStarC`. -/
instance instStarRing : StarRing (GrRingOfC R) where
  star a := ⟨R.grStarC a.coeff⟩
  star_involutive a := by
    ext k
    show R.grStarC (R.grStarC a.coeff) k = a.coeff k
    unfold grStarC
    simp [R.star_star]
  star_mul a b := by
    ext k
    change R.grStarC (R.grMulC a.coeff b.coeff) k =
         (R.grMulC (R.grStarC b.coeff) (R.grStarC a.coeff)) k
    unfold grStarC grMulC


    simp only [map_sum, map_mul, Complex.conj_natCast]

    conv_rhs =>
      rw [← Equiv.sum_comp R.starEquivC]
      arg 2; ext p; rw [← Equiv.sum_comp R.starEquivC]
    simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]


    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show R.N (R.star j) (R.star i) k = R.N i j (R.star k) from R.N_star_reverse i j k]


    rw [Finset.sum_comm]


    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show R.grStarC (fun k => a.coeff k + b.coeff k) k =
         R.grStarC a.coeff k + R.grStarC b.coeff k
    unfold grStarC; simp [map_add]

/-- The star-module compatibility on `GrRingOfC R` over ℂ: `star (c • a) = conj c • star a`. -/
instance instStarModule : StarModule ℂ (GrRingOfC R) where
  star_smul c a := by
    ext k
    show R.grStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * R.grStarC a.coeff k
    unfold grStarC
    simp [map_mul]

/-- `GrRingOfC R` is finite-dimensional as a ℂ-vector space (since `ι` is finite). -/
instance instFiniteDimensional : FiniteDimensional ℂ (GrRingOfC R) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] GrRingOfC R from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

/-- The trace `GrRingOfC R →ₗ[ℂ] ℂ` reading off the coefficient at the unit. -/
def traceLinMap : GrRingOfC R →ₗ[ℂ] ℂ where
  toFun a := R.grTraceC a.coeff
  map_add' a b := by
    show R.grTraceC (fun k => a.coeff k + b.coeff k) = R.grTraceC a.coeff + R.grTraceC b.coeff
    unfold grTraceC; rfl
  map_smul' c a := by
    change R.grTraceC (fun k => c * a.coeff k) = c * R.grTraceC a.coeff
    unfold grTraceC; rfl

end GrRingOfC

/-- Package the complexified Grothendieck ring of a fusion ring as a `*`-algebra with trace,
combining the star-ring, ℂ-algebra and trace data with its positive-definiteness. -/
def grStarAlgWithTrace : StarAlgWithTrace where
  carrier := GrRingOfC R
  trace := GrRingOfC.traceLinMap
  trace_comm a b := by
    show R.grTraceC (R.grMulC a.coeff b.coeff) = R.grTraceC (R.grMulC b.coeff a.coeff)
    exact R.trace_comm_grC a.coeff b.coeff
  trace_pos_def a ha := by
    show 0 < (R.grTraceC (R.grMulC a.coeff (R.grStarC a.coeff))).re
    apply R.trace_pos_def_grC
    intro h; apply ha; ext k; exact congrFun h k

/-- The complexified Grothendieck ring of a fusion ring is semisimple, via the general
semisimplicity theorem for finite-dimensional `*`-algebras with trace. -/
theorem complexified_grothendieck_ring_semisimple :
    IsSemisimpleRing (GrRingOfC R) :=
  @StarAlgWithTrace.starAlgWithTrace_isSemisimple R.grStarAlgWithTrace
    GrRingOfC.instFiniteDimensional

/-- The coefficient function of the `n`th power of `basisVecC i` (regarded in `GrRingOfC R`)
equals the iterated multiplication `grPowC R (basisVecC i) n`. -/
lemma GrRingOfC_pow_coeff (i : ι) (n : ℕ) :
    ((⟨basisVecC i⟩ : GrRingOfC R) ^ n).coeff = grPowC R (basisVecC i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    show (R.grMulC ((⟨basisVecC i⟩ : GrRingOfC R) ^ n).coeff (basisVecC i)) =
         R.grMulC (grPowC R (basisVecC i) n) (basisVecC i)
    rw [ih]

/-- The trace of the `n`th power of `basisVecC i` (regarded in `GrRingOfC R`) equals
`R.grTraceC (grPowC R (basisVecC i) n)`. -/
lemma GrRingOfC_traceLinMap_pow (i : ι) (n : ℕ) :
    GrRingOfC.traceLinMap (R := R) ((⟨basisVecC i⟩ : GrRingOfC R) ^ n) =
    R.grTraceC (grPowC R (basisVecC i) n) := by
  show R.grTraceC ((⟨basisVecC i⟩ : GrRingOfC R) ^ n).coeff =
       R.grTraceC (grPowC R (basisVecC i) n)
  rw [GrRingOfC_pow_coeff]

/-- The trace of an algebra-evaluated polynomial decomposes coefficient-wise as
`∑ n, p.coeff n * trace(x^n)`. -/
lemma trace_aeval_eq_sum_GrRingOfC (p : Polynomial ℂ) (x : GrRingOfC R) :
    GrRingOfC.traceLinMap (R := R) (Polynomial.aeval x p) =
    p.sum (fun n (a : ℂ) => a * GrRingOfC.traceLinMap (R := R) (x ^ n)) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum, Polynomial.sum]
  rw [map_sum]
  congr 1
  ext n
  show GrRingOfC.traceLinMap (R := R) ((algebraMap ℂ (GrRingOfC R)) (p.coeff n) * x ^ n) =
       p.coeff n * GrRingOfC.traceLinMap (R := R) (x ^ n)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]

/-- If `p` has zero constant term and `trace(x^n)` vanishes for every positive `n`, then the
trace of `aeval x p` vanishes. -/
lemma trace_aeval_zero_of_zero_const (p : Polynomial ℂ) (x : GrRingOfC R)
    (hp0 : p.coeff 0 = 0)
    (hτ : ∀ n : ℕ, 0 < n → GrRingOfC.traceLinMap (R := R) (x ^ n) = 0) :
    GrRingOfC.traceLinMap (R := R) (Polynomial.aeval x p) = 0 := by
  rw [trace_aeval_eq_sum_GrRingOfC]
  apply Finset.sum_eq_zero
  intro n hn
  show p.coeff n * GrRingOfC.traceLinMap (R := R) (x ^ n) = 0
  by_cases h0 : n = 0
  · subst h0; simp [hp0]
  · rw [hτ n (Nat.pos_of_ne_zero h0), mul_zero]

/-- In a finite-dimensional ℂ-algebra, if `x` is not nilpotent then some polynomial `p` with
zero constant term has `aeval x p` a nonzero idempotent: split the minimal polynomial as
`X^k · q` with `q` coprime to `X^k`, then use Bezout to construct orthogonal idempotents. -/
theorem exists_nonzero_idempotent_poly_of_not_nilpotent
    {A : Type*} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    (x : A) (hx : ¬IsNilpotent x) :
    ∃ (p : Polynomial ℂ), p.coeff 0 = 0 ∧
      IsIdempotentElem (Polynomial.aeval x p) ∧
      Polynomial.aeval x p ≠ 0 := by
  by_cases h0 : (minpoly ℂ x).eval 0 = 0
  ·

    set mp := minpoly ℂ x with hmp_def
    have hmp_ne : mp ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite ℂ x)
    set k := mp.rootMultiplicity 0 with hk_def
    have hk_pos : 0 < k := by
      rw [hk_def, Polynomial.rootMultiplicity_pos hmp_ne]; exact h0
    obtain ⟨q, hfact, hq_ndvd⟩ := mp.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hmp_ne (0 : ℂ)
    simp only [map_zero, sub_zero] at hfact hq_ndvd
    have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hfact; exact hmp_ne hfact

    have hcop : IsCoprime (Polynomial.X ^ k : Polynomial ℂ) q := by
      rw [isCoprime_comm]
      exact (Polynomial.irreducible_X (R := ℂ)).coprime_pow_of_not_dvd k hq_ndvd

    obtain ⟨u, v, huv⟩ := hcop

    have hef_sum : Polynomial.aeval x (u * Polynomial.X ^ k) +
        Polynomial.aeval x (v * q) = 1 := by
      rw [← map_add, huv]; simp
    have hef_prod : Polynomial.aeval x (u * Polynomial.X ^ k) *
        Polynomial.aeval x (v * q) = 0 := by
      rw [← map_mul]
      have : u * Polynomial.X ^ k * (v * q) = u * v * (Polynomial.X ^ k * q) := by ring
      rw [this, ← hfact, hmp_def, map_mul, minpoly.aeval, mul_zero]
    refine ⟨u * Polynomial.X ^ k, ?_, ?_, ?_⟩
    ·
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_antidiagonal] at hij
      have hi : i = 0 := (Nat.eq_zero_of_add_eq_zero hij).1
      have hj : j = 0 := (Nat.eq_zero_of_add_eq_zero hij).2
      subst hi; subst hj
      have : (Polynomial.X ^ k : Polynomial ℂ).coeff 0 = 0 := by
        rw [Polynomial.coeff_X_pow, if_neg]; omega
      simp [this]
    ·
      rw [IsIdempotentElem]
      have : Polynomial.aeval x (u * Polynomial.X ^ k) *
          (Polynomial.aeval x (u * Polynomial.X ^ k) +
           Polynomial.aeval x (v * q)) =
          Polynomial.aeval x (u * Polynomial.X ^ k) * 1 := by rw [hef_sum]
      rw [mul_add, hef_prod, add_zero, mul_one] at this
      exact this
    ·

      intro he0
      apply hx
      have hf1 : Polynomial.aeval x (v * q) = 1 := by
        have := hef_sum; rw [he0, zero_add] at this; exact this
      rw [map_mul] at hf1
      have hq_unit : IsUnit (Polynomial.aeval x q) := by
        have hcomm : Polynomial.aeval x q * Polynomial.aeval x v = 1 := by
          have heq : Polynomial.aeval x v * Polynomial.aeval x q =
                     Polynomial.aeval x q * Polynomial.aeval x v := by
            simp [← map_mul, mul_comm]
          rw [← heq]; exact hf1
        exact ⟨⟨Polynomial.aeval x q, Polynomial.aeval x v, hcomm, hf1⟩, rfl⟩
      have hmpx : Polynomial.aeval x (Polynomial.X ^ k * q) = 0 := by
        rw [← hfact, hmp_def]; exact minpoly.aeval ℂ x
      simp only [map_mul, map_pow, Polynomial.aeval_X] at hmpx
      exact ⟨k, (hq_unit.mul_left_eq_zero).mp hmpx⟩
  ·

    have hXndvd : ¬(Polynomial.X : Polynomial ℂ) ∣ minpoly ℂ x := by
      intro ⟨q, hq⟩; exact h0 (by simp [hq])
    have hcop : IsCoprime (Polynomial.X : Polynomial ℂ) (minpoly ℂ x) :=
      (Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hXndvd

    obtain ⟨u, v, huv⟩ := hcop

    have haeval : Polynomial.aeval x (u * Polynomial.X) = 1 := by
      have h1 : Polynomial.aeval x (u * Polynomial.X + v * minpoly ℂ x) =
        Polynomial.aeval x (1 : Polynomial ℂ) := by rw [huv]
      simp [map_add, map_mul, minpoly.aeval] at h1
      simp [map_mul, Polynomial.aeval_X]; exact h1
    refine ⟨u * Polynomial.X, ?_, ?_, ?_⟩
    · simp [Polynomial.coeff_mul, Polynomial.coeff_X]
    · rw [IsIdempotentElem, haeval, mul_one]
    · rw [haeval]
      intro h1eq0
      apply hx
      have : Subsingleton A := subsingleton_of_zero_eq_one (h1eq0.symm)
      exact ⟨1, Subsingleton.elim _ _⟩

/-- Corollary 1.43.6: for any basis element `i` of a fusion ring, some positive power has
positive real trace. Combine the idempotent-polynomial construction with positive definiteness
of the trace on `GrRingOfC R`. -/
theorem exists_pos_trace_power_general (i : ι) :
    ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC i) n)).re := by


  by_contra h_all
  push_neg at h_all


  have hzero : ∀ n, 0 < n → R.grTraceC (grPowC R (basisVecC i) n) = 0 := by
    intro n hn
    obtain ⟨m, hm⟩ := R.grPowC_basisVecC_nonneg i n R.unit
    have hle := h_all n hn
    unfold grTraceC at hle ⊢
    rw [hm]
    rw [hm] at hle
    simp only [Complex.natCast_re] at hle
    have : m = 0 := Nat.cast_eq_zero.mp (le_antisymm hle (Nat.cast_nonneg m))
    simp [this]

  let x : GrRingOfC R := ⟨basisVecC i⟩
  have hx_not_nil : ¬IsNilpotent x := by
    intro ⟨n, hn⟩
    cases n with
    | zero =>
      rw [pow_zero] at hn
      have : (1 : GrRingOfC R).coeff R.unit = (0 : GrRingOfC R).coeff R.unit :=
        congrArg (·.coeff R.unit) hn
      simp at this
    | succ n =>
      have hne := R.grPowC_basisVecC_ne_zero i (n + 1) (by omega)
      obtain ⟨k, hk⟩ := hne
      have : grPowC R (basisVecC i) (n + 1) k = 0 := by
        have hcoeff : (x ^ (n + 1)).coeff = grPowC R (basisVecC i) (n + 1) :=
          R.GrRingOfC_pow_coeff i (n + 1)
        have : (x ^ (n + 1) : GrRingOfC R) = 0 := hn
        have : (x ^ (n + 1) : GrRingOfC R).coeff k = (0 : GrRingOfC R).coeff k :=
          congrFun (congrArg GrRingOfC.coeff this) k
        rw [hcoeff] at this
        simpa using this
      rw [this] at hk; simp at hk


  obtain ⟨p, hp0, hp_idem, hp_ne⟩ :=
    exists_nonzero_idempotent_poly_of_not_nilpotent x hx_not_nil

  let B := R.grStarAlgWithTrace
  have hp_idem' : (Polynomial.aeval x p) * (Polynomial.aeval x p) = Polynomial.aeval x p :=
    hp_idem
  have hτ_pos : 0 < (B.trace (Polynomial.aeval x p)).re :=
    B.trace_pos_of_idempotent (Polynomial.aeval x p) hp_idem' hp_ne


  have hτ_xn : ∀ n : ℕ, 0 < n → GrRingOfC.traceLinMap (R := R) (x ^ n) = 0 := by
    intro n hn
    rw [R.GrRingOfC_traceLinMap_pow i n]
    exact hzero n hn
  have hτ_px : GrRingOfC.traceLinMap (R := R) (Polynomial.aeval x p) = 0 :=
    R.trace_aeval_zero_of_zero_const p x hp0 hτ_xn


  have : B.trace (Polynomial.aeval x p) =
         GrRingOfC.traceLinMap (R := R) (Polynomial.aeval x p) := rfl
  rw [this, hτ_px] at hτ_pos
  simp at hτ_pos

end

end FusionRing

/-- Corollary 1.43.5 (fusion-ring version): the complexified Grothendieck ring of any fusion
ring is semisimple. -/
theorem corollary_1_43_5_fusion {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι) :
    IsSemisimpleRing (FusionRing.GrRingOfC R) :=
  R.complexified_grothendieck_ring_semisimple
