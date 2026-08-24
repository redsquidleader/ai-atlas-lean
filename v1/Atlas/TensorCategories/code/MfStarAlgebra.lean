/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.StarAlgebra
import Atlas.TensorCategories.code.BasedRings
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The duality involution `R.star : ι → ι` of a multifusion ring packaged as an equivalence. -/
def mfStarEquiv : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- Complexified multiplication on the Grothendieck ring of a multifusion ring,
defined via the structure constants `N i j k`. -/
def mfGrMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- Complex-antilinear involution on the Grothendieck ring of a multifusion ring,
defined by complex conjugation composed with the duality involution. -/
def mfGrStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace on the complexified Grothendieck ring of a multifusion ring,
given by summing the coefficients of the unit components. -/
def mfGrTraceC (f : ι → ℂ) : ℂ := ∑ k ∈ R.I₀, f k

/-- The multiplicative identity of the complexified Grothendieck ring,
the indicator function of the set of unit components `R.I₀`. -/
def mfOneC : ι → ℂ := fun k => if k ∈ R.I₀ then 1 else 0

/-- The duality involution `star` exchanges the two arguments of an equality `i = R.star j`. -/
lemma star_eq_swap (i j : ι) : (i = R.star j) ↔ (j = R.star i) :=
  ⟨fun h => by rw [← R.star_star j, h], fun h => by rw [h, R.star_star]⟩

/-- Picks out the unique term `g (R.star i)` from a sum over `j` of indicators `i = R.star j`. -/
lemma sum_ite_star_eq (i : ι) (g : ι → ℂ) :
    (∑ j, if i = R.star j then g j else 0) = g (R.star i) := by
  have : ∀ j, (if i = R.star j then g j else (0 : ℂ)) =
    (if j = R.star i then g j else 0) := by
    intro j
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((star_eq_swap R i j).mp h1) h2
    · exact absurd ((star_eq_swap R i j).mpr h2) h1
    · rfl
  simp_rw [this, sum_ite_eq', mem_univ, if_true]

/-- Rewrites a sum over all of `ι` of a function with an indicator `i ∈ S` as a sum over `S`. -/
lemma sum_ite_mem_eq (S : Finset ι) (g : ι → ℂ) :
    (∑ i : ι, if i ∈ S then g i else 0) = ∑ i ∈ S, g i := by
  rw [← Finset.sum_filter]; congr 1; ext x; simp

/-- Complex version of the left unit relation: summing structure constants `N s j k`
over `s` in the unit components gives the Kronecker delta in `j, k`. -/
lemma sum_I₀_mul_left_complex (j k : ι) :
    (∑ s ∈ R.I₀, (R.N s j k : ℂ)) = if j = k then 1 else 0 := by
  exact_mod_cast R.sum_I₀_mul_left j k

/-- Complex version of the right unit relation: summing structure constants `N i s k`
over `s` in the unit components gives the Kronecker delta in `i, k`. -/
lemma sum_I₀_mul_right_complex (i k : ι) :
    (∑ s ∈ R.I₀, (R.N i s k : ℂ)) = if i = k then 1 else 0 := by
  exact_mod_cast R.sum_I₀_mul_right i k

/-- Complex form of the associativity relation for structure constants of a multifusion ring. -/
lemma assoc_complex (i j k l : ι) :
    (univ.sum fun m => (R.N i j m : ℂ) * (R.N m k l : ℂ)) =
    (univ.sum fun m => (R.N j k m : ℂ) * (R.N i m l : ℂ)) := by
  exact_mod_cast R.assoc i j k l

/-- Left identity law for the complexified Grothendieck-ring multiplication. -/
theorem mfGrMulC_one_left (f : ι → ℂ) :
    R.mfGrMulC (R.mfOneC) f = f := by
  funext k; unfold mfGrMulC mfOneC
  simp_rw [ite_mul, one_mul, zero_mul]
  conv_lhs =>
    arg 2; ext i
    rw [show (∑ j, (if i ∈ R.I₀ then f j * (R.N i j k : ℂ) else 0)) =
        if i ∈ R.I₀ then ∑ j, f j * (R.N i j k : ℂ) else 0
      from by split_ifs <;> simp_all]
  rw [sum_ite_mem_eq R.I₀]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [R.sum_I₀_mul_left_complex, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true]

/-- Right identity law for the complexified Grothendieck-ring multiplication. -/
theorem mfGrMulC_one_right (f : ι → ℂ) :
    R.mfGrMulC f (R.mfOneC) = f := by
  funext k; unfold mfGrMulC mfOneC
  simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [show (if j ∈ R.I₀ then f i * (R.N i j k : ℂ) else 0) =
        f i * (if j ∈ R.I₀ then (R.N i j k : ℂ) else 0)
      from by split_ifs <;> simp]
  simp_rw [← Finset.mul_sum, sum_ite_mem_eq R.I₀]
  simp_rw [R.sum_I₀_mul_right_complex, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, if_true]

/-- Inner reindexing step in the proof of associativity of `mfGrMulC`: equates the two
inner sums coming from the two associativity expansions. -/
lemma mf_inner_sum_eq (a b c : ι → ℂ) (l i j k : ι) :
    (∑ m : ι, a i * (b j * (c k * ((R.N i j m : ℂ) * (R.N m k l : ℂ))))) =
    (∑ q : ι, a i * (b j * (c k * ((R.N j k q : ℂ) * (R.N i q l : ℂ))))) := by
  simp_rw [← Finset.mul_sum]
  congr 3
  exact R.assoc_complex i j k l

/-- Associativity of the complexified Grothendieck-ring multiplication. -/
theorem mfGrMulC_assoc (a b c : ι → ℂ) :
    R.mfGrMulC (R.mfGrMulC a b) c = R.mfGrMulC a (R.mfGrMulC b c) := by
  funext l; simp only [mfGrMulC]
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
    exact R.mf_inner_sum_eq a b c l i j k

/-- Left distributivity of the complexified Grothendieck-ring multiplication over addition. -/
theorem mfGrMulC_left_distrib (a b c : ι → ℂ) :
    R.mfGrMulC a (fun k => b k + c k) = fun k => R.mfGrMulC a b k + R.mfGrMulC a c k := by
  funext l; simp only [mfGrMulC]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

/-- Right distributivity of the complexified Grothendieck-ring multiplication over addition. -/
theorem mfGrMulC_right_distrib (a b c : ι → ℂ) :
    R.mfGrMulC (fun k => a k + b k) c = fun k => R.mfGrMulC a c k + R.mfGrMulC b c k := by
  funext l; simp only [mfGrMulC]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- Multiplication by zero on the right yields zero in the complexified Grothendieck ring. -/
theorem mfGrMulC_zero (a : ι → ℂ) :
    R.mfGrMulC a (fun _ => 0) = fun _ => 0 := by
  funext l; simp only [mfGrMulC]; simp

/-- Multiplication by zero on the left yields zero in the complexified Grothendieck ring. -/
theorem mfZeroC_mul (a : ι → ℂ) :
    R.mfGrMulC (fun _ => 0) a = fun _ => 0 := by
  funext l; simp only [mfGrMulC]; simp

/-- Left scalar compatibility: scaling the left factor by `c` scales the product by `c`. -/
theorem mfGrMulC_smul_left (c : ℂ) (a b : ι → ℂ) :
    R.mfGrMulC (fun k => c * a k) b = fun k => c * R.mfGrMulC a b k := by
  funext l; simp only [mfGrMulC]
  simp_rw [mul_assoc, Finset.mul_sum]

/-- Duality identity for structure constants: `N(j*, i*, k) = N(i, j, k*)`. -/
lemma mf_N_star_reverse (i j k : ι) :
    R.N (R.star j) (R.star i) k = R.N i j (R.star k) := by
  rw [R.star_anti (R.star j) (R.star i) k, R.star_star, R.star_star]

/-- Multiplying on the left by a scalar multiple of the unit is the same as scaling. -/
theorem mfGrMulC_scalar_left (c : ℂ) (f : ι → ℂ) :
    R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) f =
    fun k => c * R.mfGrMulC (R.mfOneC) f k := by
  funext l; unfold mfGrMulC mfOneC
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split_ifs <;> ring

/-- Multiplying on the right by a scalar multiple of the unit is the same as scaling. -/
theorem mfGrMulC_scalar_right (c : ℂ) (f : ι → ℂ) :
    R.mfGrMulC f (fun k => if k ∈ R.I₀ then c else 0) =
    fun k => c * R.mfGrMulC f (R.mfOneC) k := by
  funext l; unfold mfGrMulC mfOneC
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split_ifs <;> ring

/-- Closed-form expression for `Tr(a * b)`: it equals the duality pairing
`∑ i, a i * b (R.star i)`. -/
lemma mfGrTraceC_mul_eq (a b : ι → ℂ) :
    R.mfGrTraceC (R.mfGrMulC a b) = ∑ i, a i * b (R.star i) := by
  unfold mfGrTraceC mfGrMulC
  rw [Finset.sum_comm]
  congr 1; ext i
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j
    rw [show ∑ x ∈ R.I₀, a i * b j * (R.N i j x : ℂ) =
        a i * b j * ∑ x ∈ R.I₀, (R.N i j x : ℂ)
      from by rw [Finset.mul_sum]]
  have hdual : ∀ j, (∑ k ∈ R.I₀, (R.N i j k : ℂ)) = if i = R.star j then 1 else 0 := by
    intro j; exact_mod_cast R.duality_trace i j
  simp_rw [hdual, mul_ite, mul_one, mul_zero]
  exact sum_ite_star_eq R i (fun j => a i * b j)

/-- The trace on the complexified Grothendieck ring is cyclic: `Tr(a * b) = Tr(b * a)`. -/
theorem mf_trace_comm (a b : ι → ℂ) :
    R.mfGrTraceC (R.mfGrMulC a b) = R.mfGrTraceC (R.mfGrMulC b a) := by
  rw [mfGrTraceC_mul_eq, mfGrTraceC_mul_eq]
  rw [← Equiv.sum_comp R.mfStarEquiv (fun x => a x * b (R.star x))]
  simp only [mfStarEquiv, Equiv.coe_fn_mk, R.star_star]
  congr 1; ext x; ring

/-- The trace pairing `Tr(a * a*)` equals the sum of squared norms `∑ |a i|²`. -/
theorem mf_trace_star_mul_eq_sum_normSq (a : ι → ℂ) :
    R.mfGrTraceC (R.mfGrMulC a (R.mfGrStarC a)) =
      ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
  rw [mfGrTraceC_mul_eq]
  unfold mfGrStarC
  simp_rw [R.star_star]
  congr 1; ext i; rw [mul_conj]

/-- The real part of `Tr(a * a*)` equals the real-valued sum of squared norms `∑ |a i|²`. -/
theorem mf_trace_star_mul_re (a : ι → ℂ) :
    (R.mfGrTraceC (R.mfGrMulC a (R.mfGrStarC a))).re =
      ∑ i : ι, Complex.normSq (a i) := by
  rw [mf_trace_star_mul_eq_sum_normSq]
  simp [Complex.ofReal_re]

/-- Positive-definiteness of the trace pairing `Tr(a * a*)` on nonzero elements
of the complexified Grothendieck ring. -/
theorem mf_trace_pos_def (a : ι → ℂ) (ha : a ≠ 0) :
    0 < (R.mfGrTraceC (R.mfGrMulC a (R.mfGrStarC a))).re := by
  rw [mf_trace_star_mul_re]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

end

end MultifusionRingDef

/-- The complexified Grothendieck ring of a multifusion ring, packaged as a structure
with a single field `coeff : ι → ℂ`. -/
@[ext]
structure MfGrRingOfC {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : MultifusionRingDef ι) where
  coeff : ι → ℂ

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- Zero element of the complexified Grothendieck ring. -/
instance instZero : Zero (MfGrRingOfC R) := ⟨⟨fun _ => 0⟩⟩
/-- Multiplicative identity of the complexified Grothendieck ring, given by `R.mfOneC`. -/
instance instOne : One (MfGrRingOfC R) := ⟨⟨R.mfOneC⟩⟩

/-- Componentwise addition on the complexified Grothendieck ring. -/
instance instAdd : Add (MfGrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Componentwise negation on the complexified Grothendieck ring. -/
instance instNeg : Neg (MfGrRingOfC R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Componentwise subtraction on the complexified Grothendieck ring. -/
instance instSub : Sub (MfGrRingOfC R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Multiplication on the complexified Grothendieck ring via the structure constants `N`. -/
noncomputable instance instMul : Mul (MfGrRingOfC R) := ⟨fun a b => ⟨R.mfGrMulC a.coeff b.coeff⟩⟩

/-- Componentwise `ℕ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instSMulNat : SMul ℕ (MfGrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Componentwise `ℤ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instSMulInt : SMul ℤ (MfGrRingOfC R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Natural-number cast on the complexified Grothendieck ring: `m` is the unit `mfOneC`
scaled by `m` on the unit components. -/
instance instNatCast : NatCast (MfGrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩⟩
/-- Integer cast on the complexified Grothendieck ring: `m` is the unit scaled by `m`
on the unit components. -/
instance instIntCast : IntCast (MfGrRingOfC R) :=
  ⟨fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩⟩

/-- The coefficients of the zero element of the complexified Grothendieck ring are zero. -/
@[simp] lemma coeff_zero (k : ι) : (0 : MfGrRingOfC R).coeff k = 0 := rfl
/-- The coefficients of the unit element are `1` on `R.I₀` and `0` elsewhere. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : MfGrRingOfC R).coeff k = if k ∈ R.I₀ then 1 else 0 := rfl
/-- Addition on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_add (a b : MfGrRingOfC R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Negation on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_neg (a : MfGrRingOfC R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Subtraction on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_sub (a b : MfGrRingOfC R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- The complexified Grothendieck ring of a multifusion ring is a (noncommutative) ring. -/
noncomputable instance instRing : Ring (MfGrRingOfC R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.mfGrMulC (R.mfGrMulC a.coeff b.coeff) c.coeff) k =
         (R.mfGrMulC a.coeff (R.mfGrMulC b.coeff c.coeff)) k
    rw [R.mfGrMulC_assoc]
  one_mul a := by
    ext k
    show (R.mfGrMulC R.mfOneC a.coeff) k = a.coeff k
    rw [R.mfGrMulC_one_left]
  mul_one a := by
    ext k
    show (R.mfGrMulC a.coeff R.mfOneC) k = a.coeff k
    rw [R.mfGrMulC_one_right]
  left_distrib a b c := by
    ext k
    show (R.mfGrMulC a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.mfGrMulC a.coeff b.coeff) k + (R.mfGrMulC a.coeff c.coeff) k
    rw [R.mfGrMulC_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.mfGrMulC (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.mfGrMulC a.coeff c.coeff) k + (R.mfGrMulC b.coeff c.coeff) k
    rw [R.mfGrMulC_right_distrib]
  zero_mul a := by
    ext k
    show (R.mfGrMulC (fun _ => 0) a.coeff) k = 0
    rw [R.mfZeroC_mul]
  mul_zero a := by
    ext k
    show (R.mfGrMulC a.coeff (fun _ => 0)) k = 0
    rw [R.mfGrMulC_zero]
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
  natCast := fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩
  natCast_zero := by ext k; simp
  natCast_succ m := by
    ext k; show (if k ∈ R.I₀ then (↑(m + 1) : ℂ) else 0) =
      (if k ∈ R.I₀ then (m : ℂ) else 0) + (if k ∈ R.I₀ then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k ∈ R.I₀ then (m : ℂ) else 0⟩
  intCast_ofNat m := by
    ext k
    show (if k ∈ R.I₀ then (Int.ofNat m : ℂ) else 0) =
         (if k ∈ R.I₀ then (m : ℂ) else 0)
    simp [Int.cast_natCast]
  intCast_negSucc m := by
    ext k
    show (if k ∈ R.I₀ then (Int.negSucc m : ℂ) else 0) =
         -(if k ∈ R.I₀ then ((m + 1 : ℕ) : ℂ) else 0)
    split
    · simp [Int.negSucc_eq]
    · simp

/-- The ring homomorphism `ℂ →+* MfGrRingOfC R` sending `c` to the constant `c` on `R.I₀`. -/
noncomputable def algebraMapRingHom : ℂ →+* MfGrRingOfC R where
  toFun c := ⟨fun k => if k ∈ R.I₀ then c else 0⟩
  map_one' := by ext k; simp [MultifusionRingDef.mfOneC]
  map_mul' x y := by
    ext k
    change (if k ∈ R.I₀ then x * y else 0) =
         (R.mfGrMulC (fun k => if k ∈ R.I₀ then x else 0)
                   (fun k => if k ∈ R.I₀ then y else 0)) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left]
    split <;> simp_all
  map_zero' := by ext k; simp
  map_add' x y := by
    ext k; change (if k ∈ R.I₀ then x + y else 0) =
         (if k ∈ R.I₀ then x else 0) + (if k ∈ R.I₀ then y else 0)
    split <;> simp

/-- The complexified Grothendieck ring of a multifusion ring is a `ℂ`-algebra. -/
noncomputable instance instAlgebra : Algebra ℂ (MfGrRingOfC R) where
  smul c a := ⟨fun k => c * a.coeff k⟩
  algebraMap := algebraMapRingHom
  commutes' c a := by
    ext k
    change (R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) a.coeff) k =
         (R.mfGrMulC a.coeff (fun k => if k ∈ R.I₀ then c else 0)) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left,
        R.mfGrMulC_scalar_right, R.mfGrMulC_one_right]
  smul_def' c a := by
    ext k
    change c * a.coeff k =
         (R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) a.coeff) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left]

/-- Star-ring structure on the complexified Grothendieck ring: the anti-involution
given by complex conjugation composed with duality. -/
noncomputable instance instStarRing : StarRing (MfGrRingOfC R) where
  star a := ⟨R.mfGrStarC a.coeff⟩
  star_involutive a := by
    ext k
    show R.mfGrStarC (R.mfGrStarC a.coeff) k = a.coeff k
    unfold MultifusionRingDef.mfGrStarC
    simp [R.star_star]
  star_mul a b := by
    ext k
    change R.mfGrStarC (R.mfGrMulC a.coeff b.coeff) k =
         (R.mfGrMulC (R.mfGrStarC b.coeff) (R.mfGrStarC a.coeff)) k
    unfold MultifusionRingDef.mfGrStarC MultifusionRingDef.mfGrMulC
    simp only [map_sum, map_mul, Complex.conj_natCast]
    conv_rhs =>
      rw [← Equiv.sum_comp R.mfStarEquiv]
      arg 2; ext p; rw [← Equiv.sum_comp R.mfStarEquiv]
    simp only [MultifusionRingDef.mfStarEquiv, Equiv.coe_fn_mk, R.star_star]
    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show R.N (R.star j) (R.star i) k = R.N i j (R.star k) from R.mf_N_star_reverse i j k]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show R.mfGrStarC (fun k => a.coeff k + b.coeff k) k =
         R.mfGrStarC a.coeff k + R.mfGrStarC b.coeff k
    unfold MultifusionRingDef.mfGrStarC; simp [map_add]

/-- Compatibility of the star and the `ℂ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instStarModule : StarModule ℂ (MfGrRingOfC R) where
  star_smul c a := by
    ext k
    show R.mfGrStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * R.mfGrStarC a.coeff k
    unfold MultifusionRingDef.mfGrStarC
    simp [map_mul]

/-- The complexified Grothendieck ring is finite-dimensional over `ℂ`. -/
noncomputable instance instFiniteDimensional : FiniteDimensional ℂ (MfGrRingOfC R) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] MfGrRingOfC R from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

/-- The trace `Tr : MfGrRingOfC R →ₗ[ℂ] ℂ` as a `ℂ`-linear map. -/
noncomputable def traceLinMap : MfGrRingOfC R →ₗ[ℂ] ℂ where
  toFun a := R.mfGrTraceC a.coeff
  map_add' a b := by
    show R.mfGrTraceC (fun k => a.coeff k + b.coeff k) = R.mfGrTraceC a.coeff + R.mfGrTraceC b.coeff
    unfold MultifusionRingDef.mfGrTraceC
    rw [Finset.sum_add_distrib]
  map_smul' c a := by
    change R.mfGrTraceC (fun k => c * a.coeff k) = c * R.mfGrTraceC a.coeff
    unfold MultifusionRingDef.mfGrTraceC
    rw [Finset.mul_sum]

end MfGrRingOfC

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The complexified Grothendieck ring of a multifusion ring, packaged as a
`StarAlgWithTrace` with cyclic positive-definite trace pairing. -/
noncomputable def mfGrStarAlgWithTrace : StarAlgWithTrace where
  carrier := MfGrRingOfC R
  trace := MfGrRingOfC.traceLinMap
  trace_comm a b := by
    show R.mfGrTraceC (R.mfGrMulC a.coeff b.coeff) = R.mfGrTraceC (R.mfGrMulC b.coeff a.coeff)
    exact R.mf_trace_comm a.coeff b.coeff
  trace_pos_def a ha := by
    show 0 < (R.mfGrTraceC (R.mfGrMulC a.coeff (R.mfGrStarC a.coeff))).re
    apply R.mf_trace_pos_def
    intro h; apply ha; ext k; exact congrFun h k

/-- The complexified Grothendieck ring of a multifusion ring is a semisimple ring,
obtained as a consequence of the positive-definite trace pairing. -/
theorem mf_complexified_semisimple :
    IsSemisimpleRing (MfGrRingOfC R) :=
  @StarAlgWithTrace.starAlgWithTrace_isSemisimple R.mfGrStarAlgWithTrace
    MfGrRingOfC.instFiniteDimensional

end MultifusionRingDef
