/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.StarAlgebra
import Atlas.TensorCategories.code.BasedRings
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open Finset Complex

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι)

noncomputable section

/-- Multiplication on the complexified multifusion Grothendieck ring: `(f * g) k =
∑_{i, j} f i * g j * N_{i,j}^k`. -/
def mfGrMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (M.N i j k : ℂ)

/-- Star operation on the complexified multifusion Grothendieck ring, induced by the
involution on basis labels via complex conjugation of coordinates. -/
def mfGrStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (M.star i))

/-- Trace on the complexified multifusion Grothendieck ring: sum of the coordinates over
the set of unit basis elements `I₀`. -/
def mfGrTraceC (f : ι → ℂ) : ℂ := ∑ k ∈ M.I₀, f k

/-- The star involution on basis labels packaged as an equivalence `ι ≃ ι`. -/
def mfStarEquiv : ι ≃ ι where
  toFun := M.star
  invFun := M.star
  left_inv := M.star_star
  right_inv := M.star_star

/-- Complex cast of the associativity identity for the structure constants `N i j k`. -/
lemma mf_assoc_complex (i j k l : ι) :
    (univ.sum fun m => (M.N i j m : ℂ) * (M.N m k l : ℂ)) =
    (univ.sum fun m => (M.N j k m : ℂ) * (M.N i m l : ℂ)) := by
  exact_mod_cast M.assoc i j k l

/-- Associativity of the complexified multifusion multiplication. -/
theorem mfGrMulC_assoc (a b c : ι → ℂ) :
    M.mfGrMulC (M.mfGrMulC a b) c = M.mfGrMulC a (M.mfGrMulC b c) := by
  sorry

/-- The characteristic function of the unit subset `I₀` is a left unit for `mfGrMulC`. -/
theorem mfGrMulC_one_left (f : ι → ℂ) :
    M.mfGrMulC (fun k => if k ∈ M.I₀ then 1 else 0) f = f := by
  sorry

/-- The characteristic function of the unit subset `I₀` is a right unit for `mfGrMulC`. -/
theorem mfGrMulC_one_right (f : ι → ℂ) :
    M.mfGrMulC f (fun k => if k ∈ M.I₀ then 1 else 0) = f := by
  sorry

/-- Left distributivity of `mfGrMulC` over coordinate-wise addition. -/
theorem mfGrMulC_left_distrib (a b c : ι → ℂ) :
    M.mfGrMulC a (fun k => b k + c k) = fun k => M.mfGrMulC a b k + M.mfGrMulC a c k := by
  funext l; simp only [mfGrMulC]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

/-- Right distributivity of `mfGrMulC` over coordinate-wise addition. -/
theorem mfGrMulC_right_distrib (a b c : ι → ℂ) :
    M.mfGrMulC (fun k => a k + b k) c = fun k => M.mfGrMulC a c k + M.mfGrMulC b c k := by
  funext l; simp only [mfGrMulC]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- Right multiplication by zero annihilates in the complexified Grothendieck ring. -/
theorem mfGrMulC_zero (a : ι → ℂ) :
    M.mfGrMulC a (fun _ => 0) = fun _ => 0 := by
  funext l; simp only [mfGrMulC]; simp

/-- Left multiplication by zero annihilates in the complexified Grothendieck ring. -/
theorem mfGrZeroC_mul (a : ι → ℂ) :
    M.mfGrMulC (fun _ => 0) a = fun _ => 0 := by
  funext l; simp only [mfGrMulC]; simp

/-- Left multiplication by the scalar `c` on `I₀` factors as `c` times the unit-left
multiplication. -/
theorem mfGrMulC_scalar_left (c : ℂ) (f : ι → ℂ) :
    M.mfGrMulC (fun k => if k ∈ M.I₀ then c else 0) f =
    fun k => c * M.mfGrMulC (fun k => if k ∈ M.I₀ then 1 else 0) f k := by
  funext l; unfold mfGrMulC
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

/-- Right multiplication by the scalar `c` on `I₀` factors as `c` times the unit-right
multiplication. -/
theorem mfGrMulC_scalar_right (c : ℂ) (f : ι → ℂ) :
    M.mfGrMulC f (fun k => if k ∈ M.I₀ then c else 0) =
    fun k => c * M.mfGrMulC f (fun k => if k ∈ M.I₀ then 1 else 0) k := by
  funext l; unfold mfGrMulC
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.mul_sum]
  congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  split <;> ring

/-- Cyclic property of the trace on the complexified Grothendieck ring. -/
theorem mf_trace_comm (a b : ι → ℂ) :
    M.mfGrTraceC (M.mfGrMulC a b) = M.mfGrTraceC (M.mfGrMulC b a) := by
  sorry

/-- The trace of `a * a*` equals `∑ i ‖a i‖²` (as a complex number). -/
theorem mf_trace_star_mul_eq_sum_normSq (a : ι → ℂ) :
    M.mfGrTraceC (M.mfGrMulC a (M.mfGrStarC a)) =
      ∑ i : ι, (Complex.normSq (a i) : ℂ) := by
  sorry

/-- Real part version of `mf_trace_star_mul_eq_sum_normSq`. -/
theorem mf_trace_star_mul_re (a : ι → ℂ) :
    (M.mfGrTraceC (M.mfGrMulC a (M.mfGrStarC a))).re =
      ∑ i : ι, Complex.normSq (a i) := by
  rw [mf_trace_star_mul_eq_sum_normSq]
  simp [Complex.ofReal_re]

/-- Positive-definiteness of the trace `tr(a a*)` on the complexified Grothendieck ring. -/
theorem mf_trace_pos_def (a : ι → ℂ) (ha : a ≠ 0) :
    0 < (M.mfGrTraceC (M.mfGrMulC a (M.mfGrStarC a))).re := by
  rw [mf_trace_star_mul_re]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- The complexified multifusion Grothendieck ring as a structure with a coordinate
function `coeff : ι → ℂ`. -/
@[ext]
structure MfGrRingOfC (M : MultifusionRingDef ι) where
  coeff : ι → ℂ

namespace MfGrRingOfC

variable {M : MultifusionRingDef ι}

/-- Zero element of `MfGrRingOfC M`: the constant-zero coordinate function. -/
instance instZero : Zero (MfGrRingOfC M) := ⟨⟨fun _ => 0⟩⟩
/-- Unit element of `MfGrRingOfC M`: the indicator function of the unit subset `I₀`. -/
instance instOne : One (MfGrRingOfC M) := ⟨⟨fun k => if k ∈ M.I₀ then 1 else 0⟩⟩

/-- Coordinate-wise addition on `MfGrRingOfC M`. -/
instance instAdd : Add (MfGrRingOfC M) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Coordinate-wise negation on `MfGrRingOfC M`. -/
instance instNeg : Neg (MfGrRingOfC M) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Coordinate-wise subtraction on `MfGrRingOfC M`. -/
instance instSub : Sub (MfGrRingOfC M) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Multiplication on `MfGrRingOfC M` given by the structure constants via `mfGrMulC`. -/
instance instMul : Mul (MfGrRingOfC M) := ⟨fun a b => ⟨M.mfGrMulC a.coeff b.coeff⟩⟩

/-- Coordinate-wise `ℕ`-scalar multiplication on `MfGrRingOfC M`. -/
instance instSMulNat : SMul ℕ (MfGrRingOfC M) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Coordinate-wise `ℤ`-scalar multiplication on `MfGrRingOfC M`. -/
instance instSMulInt : SMul ℤ (MfGrRingOfC M) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Natural-number cast into `MfGrRingOfC M`: `m` becomes `m` on the unit subset and `0`
elsewhere. -/
instance instNatCast : NatCast (MfGrRingOfC M) :=
  ⟨fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩⟩
/-- Integer cast into `MfGrRingOfC M`: `m` becomes `m` on the unit subset and `0` elsewhere. -/
instance instIntCast : IntCast (MfGrRingOfC M) :=
  ⟨fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩⟩

/-- Coordinates of the zero element vanish. -/
@[simp] lemma coeff_zero (k : ι) : (0 : MfGrRingOfC M).coeff k = 0 := rfl
/-- Coordinates of the unit element are the indicator function of `I₀`. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : MfGrRingOfC M).coeff k = if k ∈ M.I₀ then 1 else 0 := rfl
/-- Coordinates of a sum are the sum of coordinates. -/
@[simp] lemma coeff_add (a b : MfGrRingOfC M) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Coordinates of a negation are the negation of coordinates. -/
@[simp] lemma coeff_neg (a : MfGrRingOfC M) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Coordinates of a difference are the coordinate-wise difference. -/
@[simp] lemma coeff_sub (a b : MfGrRingOfC M) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- Ring structure on `MfGrRingOfC M`: coordinate-wise additive group with multiplication
given by the multifusion structure constants. -/
instance instRing : Ring (MfGrRingOfC M) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (M.mfGrMulC (M.mfGrMulC a.coeff b.coeff) c.coeff) k =
         (M.mfGrMulC a.coeff (M.mfGrMulC b.coeff c.coeff)) k
    rw [M.mfGrMulC_assoc]
  one_mul a := by
    ext k
    show (M.mfGrMulC (fun k => if k ∈ M.I₀ then 1 else 0) a.coeff) k = a.coeff k
    rw [M.mfGrMulC_one_left]
  mul_one a := by
    ext k
    show (M.mfGrMulC a.coeff (fun k => if k ∈ M.I₀ then 1 else 0)) k = a.coeff k
    rw [M.mfGrMulC_one_right]
  left_distrib a b c := by
    ext k
    show (M.mfGrMulC a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (M.mfGrMulC a.coeff b.coeff) k + (M.mfGrMulC a.coeff c.coeff) k
    rw [M.mfGrMulC_left_distrib]
  right_distrib a b c := by
    ext k
    show (M.mfGrMulC (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (M.mfGrMulC a.coeff c.coeff) k + (M.mfGrMulC b.coeff c.coeff) k
    rw [M.mfGrMulC_right_distrib]
  zero_mul a := by
    ext k
    show (M.mfGrMulC (fun _ => 0) a.coeff) k = 0
    rw [M.mfGrZeroC_mul]
  mul_zero a := by
    ext k
    show (M.mfGrMulC a.coeff (fun _ => 0)) k = 0
    rw [M.mfGrMulC_zero]
  neg_add_cancel a := by ext k; simp
  sub_eq_add_neg a b := by ext k; simp [sub_eq_add_neg]
  zsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  zsmul_zero' a := by ext k; simp
  zsmul_succ' n a := by ext k; simp [add_mul, add_comm]
  zsmul_neg' n a := by
    ext k
    show Int.negSucc n • a.coeff k = -((↑(n + 1) : ℤ) • a.coeff k)
    simp [Int.negSucc_eq, Nat.cast_succ]; ring
  natCast := fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩
  natCast_zero := by ext k; simp
  natCast_succ m := by
    ext k; show (if k ∈ M.I₀ then (↑(m + 1) : ℂ) else 0) =
      (if k ∈ M.I₀ then (m : ℂ) else 0) + (if k ∈ M.I₀ then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k ∈ M.I₀ then (m : ℂ) else 0⟩
  intCast_ofNat m := by
    ext k
    show (if k ∈ M.I₀ then (Int.ofNat m : ℂ) else 0) =
         (if k ∈ M.I₀ then (m : ℂ) else 0)
    simp [Int.cast_natCast]
  intCast_negSucc m := by
    ext k
    show (if k ∈ M.I₀ then (Int.negSucc m : ℂ) else 0) =
         -(if k ∈ M.I₀ then ((m + 1 : ℕ) : ℂ) else 0)
    split
    · simp [Int.negSucc_eq]
    · simp

/-- The structure ring homomorphism `ℂ →+* MfGrRingOfC M` sending a scalar `c` to its
multiple of the unit element. -/
def mfAlgebraMapRingHom : ℂ →+* MfGrRingOfC M where
  toFun c := ⟨fun k => if k ∈ M.I₀ then c else 0⟩
  map_one' := by ext k; simp
  map_mul' x y := by
    ext k
    change (if k ∈ M.I₀ then x * y else 0) =
         (M.mfGrMulC (fun k => if k ∈ M.I₀ then x else 0)
                      (fun k => if k ∈ M.I₀ then y else 0)) k
    rw [M.mfGrMulC_scalar_left, M.mfGrMulC_one_left]
    split <;> simp_all
  map_zero' := by ext k; simp
  map_add' x y := by
    ext k; change (if k ∈ M.I₀ then x + y else 0) =
         (if k ∈ M.I₀ then x else 0) + (if k ∈ M.I₀ then y else 0)
    split <;> simp

/-- `ℂ`-algebra structure on `MfGrRingOfC M` with structure map `mfAlgebraMapRingHom`. -/
instance instAlgebra : Algebra ℂ (MfGrRingOfC M) where
  smul c a := ⟨fun k => c * a.coeff k⟩
  algebraMap := mfAlgebraMapRingHom
  commutes' c a := by
    ext k
    change (M.mfGrMulC (fun k => if k ∈ M.I₀ then c else 0) a.coeff) k =
         (M.mfGrMulC a.coeff (fun k => if k ∈ M.I₀ then c else 0)) k
    rw [M.mfGrMulC_scalar_left, M.mfGrMulC_one_left,
        M.mfGrMulC_scalar_right, M.mfGrMulC_one_right]
  smul_def' c a := by
    ext k
    change c * a.coeff k =
         (M.mfGrMulC (fun k => if k ∈ M.I₀ then c else 0) a.coeff) k
    rw [M.mfGrMulC_scalar_left, M.mfGrMulC_one_left]

/-- `StarRing` structure on `MfGrRingOfC M` induced by `mfGrStarC`: star is an involutive
antihomomorphism compatible with the multifusion structure constants. -/
instance instStarRing : StarRing (MfGrRingOfC M) where
  star a := ⟨M.mfGrStarC a.coeff⟩
  star_involutive a := by
    ext k
    show M.mfGrStarC (M.mfGrStarC a.coeff) k = a.coeff k
    unfold mfGrStarC
    simp [M.star_star]
  star_mul a b := by
    ext k
    change M.mfGrStarC (M.mfGrMulC a.coeff b.coeff) k =
         (M.mfGrMulC (M.mfGrStarC b.coeff) (M.mfGrStarC a.coeff)) k
    unfold mfGrStarC mfGrMulC
    simp only [map_sum, map_mul, Complex.conj_natCast]
    conv_rhs =>
      rw [← Equiv.sum_comp M.mfStarEquiv]
      arg 2; ext p; rw [← Equiv.sum_comp M.mfStarEquiv]
    simp only [mfStarEquiv, Equiv.coe_fn_mk, M.star_star]
    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show M.N (M.star j) (M.star i) k = M.N i j (M.star k) from by
        rw [M.star_anti]; simp [M.star_star]]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show M.mfGrStarC (fun k => a.coeff k + b.coeff k) k =
         M.mfGrStarC a.coeff k + M.mfGrStarC b.coeff k
    unfold mfGrStarC; simp [map_add]

/-- Compatibility of star and scalar multiplication: `star (c • a) = (conj c) • star a`. -/
instance instStarModule : StarModule ℂ (MfGrRingOfC M) where
  star_smul c a := by
    ext k
    show M.mfGrStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * M.mfGrStarC a.coeff k
    unfold mfGrStarC
    simp [map_mul]

/-- The complexified multifusion Grothendieck ring `MfGrRingOfC M` is finite-dimensional
over `ℂ`, with dimension at most `|ι|`. -/
instance instFiniteDimensional : FiniteDimensional ℂ (MfGrRingOfC M) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] MfGrRingOfC M from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

/-- The trace `mfGrTraceC` packaged as a `ℂ`-linear map `MfGrRingOfC M →ₗ[ℂ] ℂ`. -/
def mfTraceLinMap : MfGrRingOfC M →ₗ[ℂ] ℂ where
  toFun a := M.mfGrTraceC a.coeff
  map_add' a b := by
    show M.mfGrTraceC (fun k => a.coeff k + b.coeff k) = M.mfGrTraceC a.coeff + M.mfGrTraceC b.coeff
    unfold mfGrTraceC; rw [Finset.sum_add_distrib]
  map_smul' c a := by
    change M.mfGrTraceC (fun k => c * a.coeff k) = c * M.mfGrTraceC a.coeff
    unfold mfGrTraceC; rw [Finset.mul_sum]

end MfGrRingOfC

/-- The complexified multifusion Grothendieck ring assembled as a `StarAlgWithTrace`, with
the cyclic positive-definite trace `mfTraceLinMap`. -/
def mfGrStarAlgWithTrace : StarAlgWithTrace where
  carrier := MfGrRingOfC M
  trace := MfGrRingOfC.mfTraceLinMap
  trace_comm a b := by
    show M.mfGrTraceC (M.mfGrMulC a.coeff b.coeff) = M.mfGrTraceC (M.mfGrMulC b.coeff a.coeff)
    exact M.mf_trace_comm a.coeff b.coeff
  trace_pos_def a ha := by
    show 0 < (M.mfGrTraceC (M.mfGrMulC a.coeff (M.mfGrStarC a.coeff))).re
    apply M.mf_trace_pos_def
    intro h; apply ha; ext k; exact congrFun h k

/-- The complexified multifusion Grothendieck ring is a semisimple ring, obtained via the
`StarAlgWithTrace` semisimplicity criterion. -/
theorem mf_complexified_grothendieck_ring_semisimple :
    IsSemisimpleRing (MfGrRingOfC M) :=
  @StarAlgWithTrace.starAlgWithTrace_isSemisimple M.mfGrStarAlgWithTrace
    MfGrRingOfC.instFiniteDimensional

end

end MultifusionRingDef

/-- EGNO Corollary 1.43.5: the complexified Grothendieck ring of a multifusion ring is
semisimple. -/
theorem corollary_1_43_5 {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι) :
    IsSemisimpleRing (MultifusionRingDef.MfGrRingOfC M) :=
  M.mf_complexified_grothendieck_ring_semisimple
