/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SobolevEmbedding
import Atlas.DifferentialAnalysis.code.HilbertSpace
import Atlas.DifferentialAnalysis.code.FourierInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Affine.MazurUlam

noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- The Japanese bracket `⟨ξ⟩ := sqrt(1 + ‖ξ‖²)` used as a smooth comparison weight. -/
def japaneseBracket {E : Type*} [NormedAddCommGroup E] (ξ : E) : ℝ :=
  Real.sqrt (1 + ‖ξ‖ ^ 2)

/-- The Sobolev weight `(1 + ‖ξ‖²)^m`, the symbol used to define `H^m` via the Fourier transform. -/
def sobolevWeight {E : Type*} [NormedAddCommGroup E] (m : ℝ) (ξ : E) : ℝ :=
  ((1 : ℝ) + ‖ξ‖ ^ 2) ^ m

/-- The Japanese bracket is strictly positive. -/
theorem japaneseBracket_pos {E : Type*} [NormedAddCommGroup E] (ξ : E) :
    0 < japaneseBracket ξ := by
  simp only [japaneseBracket]
  apply Real.sqrt_pos_of_pos
  positivity

/-- The Sobolev weight is strictly positive for every real exponent. -/
theorem sobolevWeight_pos {E : Type*} [NormedAddCommGroup E] (m : ℝ) (ξ : E) :
    0 < sobolevWeight m ξ := by
  simp only [sobolevWeight]
  positivity


/-- Elements of `SobolevSpace n m` are `j`-times continuously differentiable for any `j ≤ m`. -/
theorem sobolevSpace_contDiff {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m) (j : ℕ) (hj : j ≤ m) :
    ContDiff ℝ (j : ℕ∞) u.toFun :=
  u.contDiff_toFun.of_le (Nat.cast_le.mpr hj)


/-- The `j`-th iterated Fréchet derivative of the sum of two `SobolevSpace n m` elements is in `L^2`. -/
theorem sobolevSpace_add_memLp {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have huf : ContDiff ℝ (j : ℕ∞) u.toFun := sobolevSpace_contDiff u j hj
  have hvf : ContDiff ℝ (j : ℕ∞) v.toFun := sobolevSpace_contDiff v j hj
  have heq : (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) =
      (fun x => iteratedFDeriv ℝ j u.toFun x + iteratedFDeriv ℝ j v.toFun x) := by
    ext x
    rw [iteratedFDeriv_add_apply huf.contDiffAt hvf.contDiffAt]
  rw [heq]
  exact (u.iteratedFDeriv_memLp j hj).add (v.iteratedFDeriv_memLp j hj)


/-- The triangle inequality for the `ℓ^2` norm of finite sequences indexed by `Finset.range k`. -/
lemma l2_triangle_range (k : ℕ) (a b : ℕ → ℝ) :
    Real.sqrt (∑ j ∈ Finset.range k, (a j + b j) ^ 2) ≤
    Real.sqrt (∑ j ∈ Finset.range k, (a j) ^ 2) +
    Real.sqrt (∑ j ∈ Finset.range k, (b j) ^ 2) := by
  simp_rw [Finset.sum_range]
  have h := @norm_add_le (PiLp 2 (fun _ : Fin k => ℝ)) _
    (WithLp.toLp 2 (fun i : Fin k => a i)) (WithLp.toLp 2 (fun i : Fin k => b i))
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  exact h


/-- Monotonicity of `sqrt (∑ c j ^ 2)` in pointwise nonnegative bounds `c j ≤ d j`. -/
lemma sqrt_sum_sq_mono {k : ℕ} {c d : ℕ → ℝ}
    (hc : ∀ j ∈ Finset.range k, 0 ≤ c j)
    (hle : ∀ j ∈ Finset.range k, c j ≤ d j) :
    Real.sqrt (∑ j ∈ Finset.range k, (c j) ^ 2) ≤
    Real.sqrt (∑ j ∈ Finset.range k, (d j) ^ 2) := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j hj
  exact pow_le_pow_left₀ (hc j hj) (hle j hj) 2


/-- Triangle inequality for the Sobolev `H^m` norm on `SobolevSpace n m`. -/
theorem sobolevSpace_norm_triangle {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) :
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume).toReal ^ 2) ≤
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2) +
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume).toReal ^ 2) := by

  set au := fun j => (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal
  set av := fun j => (eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume).toReal
  set auv := fun j =>
    (eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume).toReal

  have hle : ∀ j ∈ Finset.range (m + 1), auv j ≤ au j + av j := by
    intro j hj
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega

    have huf : ContDiff ℝ (j : ℕ∞) u.toFun := sobolevSpace_contDiff u j hjm
    have hvf : ContDiff ℝ (j : ℕ∞) v.toFun := sobolevSpace_contDiff v j hjm

    have heq : (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) =
        (fun x => iteratedFDeriv ℝ j u.toFun x + iteratedFDeriv ℝ j v.toFun x) := by
      ext x; rw [iteratedFDeriv_add_apply huf.contDiffAt hvf.contDiffAt]

    have hu_lp := u.iteratedFDeriv_memLp j hjm
    have hv_lp := v.iteratedFDeriv_memLp j hjm

    have hmin : eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume ≤
        eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume +
        eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume := by
      rw [heq]
      exact eLpNorm_add_le hu_lp.aestronglyMeasurable hv_lp.aestronglyMeasurable one_le_two

    have hfin : eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume +
        eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hu_lp.eLpNorm_ne_top, hv_lp.eLpNorm_ne_top⟩
    calc auv j
        = (eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume).toReal := rfl
      _ ≤ (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume +
            eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume).toReal :=
          ENNReal.toReal_mono hfin hmin
      _ = au j + av j :=
          ENNReal.toReal_add hu_lp.eLpNorm_ne_top hv_lp.eLpNorm_ne_top

  have hnn : ∀ j ∈ Finset.range (m + 1), 0 ≤ auv j := fun _ _ => ENNReal.toReal_nonneg

  calc Real.sqrt (∑ j ∈ Finset.range (m + 1), auv j ^ 2)
      ≤ Real.sqrt (∑ j ∈ Finset.range (m + 1), (au j + av j) ^ 2) :=
        sqrt_sum_sq_mono hnn hle
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (m + 1), au j ^ 2) +
        Real.sqrt (∑ j ∈ Finset.range (m + 1), av j ^ 2) :=
        l2_triangle_range (m + 1) au av


/-- A continuous Sobolev function that vanishes almost everywhere vanishes identically. -/
theorem sobolevSpace_ae_eq_zero_imp_eq_zero {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m)
    (hae : u.toFun =ᵐ[volume] 0) : u.toFun = 0 := by
  have hcont : Continuous u.toFun :=
    (sobolevSpace_contDiff u 0 (Nat.zero_le m)).continuous
  exact (hcont.ae_eq_iff_eq volume continuous_zero).mp hae

/-- Separation property: if every Sobolev semi-norm of `u` vanishes, then the underlying function is zero. -/
theorem sobolevSpace_norm_separation {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m)
    (h : ∀ j, j ≤ m →
      (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal = 0) :
    u.toFun = 0 := by

  have h0 := h 0 (Nat.zero_le m)
  have hm0 := u.iteratedFDeriv_memLp 0 (Nat.zero_le m)

  rw [ENNReal.toReal_eq_zero_iff] at h0
  have hsnorm : eLpNorm (fun x => iteratedFDeriv ℝ 0 u.toFun x) 2 volume = 0 :=
    h0.elim id (fun htop => absurd hm0.eLpNorm_lt_top (not_lt.mpr (le_of_eq htop.symm)))

  have hae : (fun x => iteratedFDeriv ℝ 0 u.toFun x) =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff hm0.1 two_ne_zero).mp hsnorm

  have hae_f : u.toFun =ᵐ[volume] 0 := by
    apply hae.mono
    intro x hx
    simp only [Pi.zero_apply] at hx ⊢
    have : ‖iteratedFDeriv ℝ 0 u.toFun x‖ = 0 := by rw [hx]; simp
    rw [norm_iteratedFDeriv_zero] at this
    exact norm_eq_zero.mp this

  exact sobolevSpace_ae_eq_zero_imp_eq_zero u hae_f


/-- Extensionality for `SobolevSpace n m`: equality is determined by the underlying function. -/
@[ext]
theorem SobolevEmbedding.SobolevSpace.ext' {n m : ℕ}
    {u v : SobolevEmbedding.SobolevSpace n m} (h : u.toFun = v.toFun) : u = v := by
  cases u; cases v; simp_all


/-- The zero element of `SobolevSpace n m`. -/
instance sobolevSpaceZero (n m : ℕ) : Zero (SobolevEmbedding.SobolevSpace n m) :=
  ⟨⟨0, contDiff_const, fun j _ => by
    have : (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) = 0 := by
      ext x; simp
    rw [this]; exact MemLp.zero⟩⟩

/-- Negation on `SobolevSpace n m`, obtained by negating the underlying function. -/
instance sobolevSpaceNeg (n m : ℕ) : Neg (SobolevEmbedding.SobolevSpace n m) :=
  ⟨fun u => ⟨-u.toFun, u.contDiff_toFun.neg, fun j hj => by
    simp only [iteratedFDeriv_neg]; exact (u.iteratedFDeriv_memLp j hj).neg⟩⟩

/-- Addition on `SobolevSpace n m`, obtained pointwise on the underlying functions. -/
instance sobolevSpaceAdd (n m : ℕ) : Add (SobolevEmbedding.SobolevSpace n m) :=
  ⟨fun u v => ⟨u.toFun + v.toFun, u.contDiff_toFun.add v.contDiff_toFun,
    fun j hj => sobolevSpace_add_memLp u v j hj⟩⟩

/-- Underlying-function form of addition on `SobolevSpace n m`. -/
@[simp] lemma sobolevSpace_add_toFun {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) : (u + v).toFun = u.toFun + v.toFun := rfl
/-- Underlying-function form of negation on `SobolevSpace n m`. -/
@[simp] lemma sobolevSpace_neg_toFun {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m) : (-u).toFun = -u.toFun := rfl
/-- The underlying function of the zero element is the zero function. -/
@[simp] lemma sobolevSpace_zero_toFun (n m : ℕ) :
    (0 : SobolevEmbedding.SobolevSpace n m).toFun = 0 := rfl

/-- The additive commutative group structure on `SobolevSpace n m`. -/
instance sobolevSpace_addCommGroup' (n m : ℕ) :
    AddCommGroup (SobolevEmbedding.SobolevSpace n m) :=
  { add_assoc := fun a b c =>
      SobolevEmbedding.SobolevSpace.ext' (add_assoc a.toFun b.toFun c.toFun)
    zero_add := fun a => SobolevEmbedding.SobolevSpace.ext' (zero_add a.toFun)
    add_zero := fun a => SobolevEmbedding.SobolevSpace.ext' (add_zero a.toFun)
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun a =>
      SobolevEmbedding.SobolevSpace.ext' (neg_add_cancel a.toFun)
    add_comm := fun a b =>
      SobolevEmbedding.SobolevSpace.ext' (add_comm a.toFun b.toFun) }

/-- The Sobolev `H^m` norm of `u`: the `ℓ^2` sum of the `L^2` norms of all iterated derivatives up to order `m`. -/
def sobolevNorm {n m : ℕ} (u : SobolevEmbedding.SobolevSpace n m) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (m + 1),
    (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2)

/-- The Sobolev norm is invariant under negation. -/
lemma sobolevNorm_neg' {n m : ℕ} (u : SobolevEmbedding.SobolevSpace n m) :
    sobolevNorm (-u) = sobolevNorm u := by
  simp only [sobolevNorm, sobolevSpace_neg_toFun, iteratedFDeriv_neg]
  congr 1; apply Finset.sum_congr rfl; intro j _
  have : (fun x => (-iteratedFDeriv ℝ j u.toFun) x) = -(fun x => iteratedFDeriv ℝ j u.toFun x) := rfl
  rw [this, eLpNorm_neg]

/-- The Sobolev norm of the zero element is zero. -/
lemma sobolevNorm_zero' (n m : ℕ) : sobolevNorm (0 : SobolevEmbedding.SobolevSpace n m) = 0 := by
  simp only [sobolevNorm, sobolevSpace_zero_toFun]
  suffices h : ∀ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) 2 volume).toReal ^ 2 = 0 by
    simp_all
  intro j _
  have : (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) = 0 := by ext x; simp
  simp [this]

/-- If the Sobolev norm of `u` is zero, then `u = 0`. -/
lemma sobolevNorm_eq_zero_iff {n m : ℕ} (u : SobolevEmbedding.SobolevSpace n m)
    (h : sobolevNorm u = 0) :
    u = 0 := by
  have hsq : ∀ j ∈ Finset.range (m + 1),
      (0 : ℝ) ≤ (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2 :=
    fun _ _ => sq_nonneg _
  have hsum := Real.sqrt_eq_zero (Finset.sum_nonneg hsq) |>.mp h
  have := Finset.sum_eq_zero_iff_of_nonneg hsq |>.mp hsum
  have hcomp : ∀ j, j ≤ m →
      (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal = 0 := by
    intro j hj
    have := this j (Finset.mem_range.mpr (by omega))
    exact sq_eq_zero_iff.mp this
  exact SobolevEmbedding.SobolevSpace.ext' (sobolevSpace_norm_separation u hcomp)

/-- The normed additive commutative group structure on `SobolevSpace n m` from the Sobolev norm. -/
abbrev sobolevSpace_nacg (n m : ℕ) :
    NormedAddCommGroup (SobolevEmbedding.SobolevSpace n m) :=
  @AddGroupNorm.toNormedAddCommGroup _ (sobolevSpace_addCommGroup' n m)
    { toFun := sobolevNorm
      map_zero' := sobolevNorm_zero' n m
      add_le' := fun u v => sobolevSpace_norm_triangle u v
      neg' := fun u => sobolevNorm_neg' u
      eq_zero_of_map_eq_zero' := fun u h => sobolevNorm_eq_zero_iff u h }


attribute [local instance] sobolevSpace_nacg


/-- The `j`-th iterated derivative of `c • u` is in `L^2` for scalar `c` and `u ∈ SobolevSpace n m`. -/
theorem sobolevSpace_smul_memLp {n m : ℕ}
    (c : ℂ) (u : SobolevEmbedding.SobolevSpace n m) (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  by_cases hc : c = 0
  ·
    subst hc
    simp only [zero_smul]
    have : (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) = 0 := by
      ext x; simp
    rw [this]
    exact MemLp.zero
  ·
    let g : ℂ ≃L[ℝ] ℂ := {
      toLinearEquiv := {
        toLinearMap := (c • (ContinuousLinearMap.id ℝ ℂ)).toLinearMap
        invFun := fun y => c⁻¹ • y
        left_inv := fun y => by simp [← mul_assoc, inv_mul_cancel₀ hc]
        right_inv := fun y => by simp [← mul_assoc, mul_inv_cancel₀ hc]
      }
      continuous_toFun := (c • (ContinuousLinearMap.id ℝ ℂ)).continuous
      continuous_invFun := (c⁻¹ • (ContinuousLinearMap.id ℝ ℂ)).continuous
    }
    have hgf : c • u.toFun = ⇑g ∘ u.toFun := by ext y; simp [g]
    have key : ∀ x, iteratedFDeriv ℝ j (c • u.toFun) x =
        g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv ℝ j u.toFun x) := by
      intro x; rw [hgf]; exact ContinuousLinearEquiv.iteratedFDeriv_comp_left g
    have key2 : ∀ x, g.toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ j u.toFun x) = c • (iteratedFDeriv ℝ j u.toFun x) := by
      intro x
      ext v
      simp [g, ContinuousLinearMap.compContinuousMultilinearMap_coe]
    have key3 : (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) =
        c • (fun x => iteratedFDeriv ℝ j u.toFun x) := by
      ext x; rw [key x, key2 x]; rfl
    rw [key3]
    exact (u.iteratedFDeriv_memLp j hj).const_smul c

/-- The scalar multiplication of `ℂ` on `SobolevSpace n m`. -/
instance sobolevSpaceSMul (n m : ℕ) : SMul ℂ (SobolevEmbedding.SobolevSpace n m) :=
  ⟨fun c u => ⟨c • u.toFun, u.contDiff_toFun.const_smul c,
    fun j hj => sobolevSpace_smul_memLp c u j hj⟩⟩

/-- Underlying-function form of scalar multiplication on `SobolevSpace n m`. -/
@[simp] lemma sobolevSpace_smul_toFun {n m : ℕ}
    (c : ℂ) (u : SobolevEmbedding.SobolevSpace n m) : (c • u).toFun = c • u.toFun := rfl

/-- The `ℂ`-module structure on `SobolevSpace n m`. -/
instance sobolevSpace_module' (n m : ℕ) :
    Module ℂ (SobolevEmbedding.SobolevSpace n m) :=
  { smul := (· • ·)
    mul_smul := fun a b u =>
      SobolevEmbedding.SobolevSpace.ext' (mul_smul a b u.toFun)
    one_smul := fun u =>
      SobolevEmbedding.SobolevSpace.ext' (one_smul ℂ u.toFun)
    smul_zero := fun a =>
      SobolevEmbedding.SobolevSpace.ext' (smul_zero a)
    smul_add := fun a u v =>
      SobolevEmbedding.SobolevSpace.ext' (smul_add a u.toFun v.toFun)
    add_smul := fun a b u =>
      SobolevEmbedding.SobolevSpace.ext' (add_smul a b u.toFun)
    zero_smul := fun u =>
      SobolevEmbedding.SobolevSpace.ext' (zero_smul ℂ u.toFun) }


/-- The Sobolev norm is homogeneous (bounded by) `‖c‖ * ‖u‖` under scalar multiplication. -/
theorem sobolevSpace_norm_smul_le {n m : ℕ}
    (c : ℂ) (u : SobolevEmbedding.SobolevSpace n m) :
    @Norm.norm _ (sobolevSpace_nacg n m).toNorm (c • u) ≤
      ‖c‖ * @Norm.norm _ (sobolevSpace_nacg n m).toNorm u := by

  show sobolevNorm (c • u) ≤ ‖c‖ * sobolevNorm u
  simp only [sobolevNorm, sobolevSpace_smul_toFun]

  have hderiv : ∀ j, j ≤ m → ∀ x : EuclideanSpace ℝ (Fin n),
      iteratedFDeriv ℝ j (c • u.toFun) x = c • iteratedFDeriv ℝ j u.toFun x := by
    intro j hj x
    exact iteratedFDeriv_const_smul_apply (sobolevSpace_contDiff u j hj).contDiffAt

  have heLp : ∀ j ∈ Finset.range (m + 1),
      eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume =
        ‖c‖ₑ * eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume := by
    intro j hj
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega
    have heq : (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) =
        c • (fun x => iteratedFDeriv ℝ j u.toFun x) := by
      ext x; simp [hderiv j hjm x]
    rw [heq]
    exact eLpNorm_const_smul c _ 2 volume

  have htoReal : ∀ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume).toReal =
        ‖c‖ * (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal := by
    intro j hj
    rw [heLp j hj, ENNReal.toReal_mul]
    simp [enorm]

  have hsq : ∀ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume).toReal ^ 2 =
        ‖c‖ ^ 2 * (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2 := by
    intro j hj
    rw [htoReal j hj, mul_pow]

  have hsum : (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume).toReal ^ 2) =
      ‖c‖ ^ 2 * (∑ j ∈ Finset.range (m + 1),
        (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2) := by
    rw [Finset.sum_congr rfl hsq, ← Finset.mul_sum]

  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

/-- The complex `NormedSpace` structure on `SobolevSpace n m`. -/
instance sobolevSpace_normedSpace' (n m : ℕ) :
    @NormedSpace ℂ (SobolevEmbedding.SobolevSpace n m) _
      (sobolevSpace_nacg n m).toSeminormedAddCommGroup :=
  @NormedSpace.mk ℂ _ _ (sobolevSpace_nacg n m).toSeminormedAddCommGroup
    (sobolevSpace_module' n m) (fun c u => sobolevSpace_norm_smul_le c u)


/-- The Fourier-side identification of `SobolevSpace n m` with `L^2` (as a bare equivalence). -/
noncomputable def sobolevFourierEquiv (n m : ℕ) :
    @Equiv (SobolevEmbedding.SobolevSpace n m)
      (MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry


/-- The Fourier-side equivalence `sobolevFourierEquiv` is an isometry between the Sobolev norm and the `L^2` norm. -/
theorem sobolevFourierEquiv_isometry (n m : ℕ) :
    @Isometry _ _
      (@EMetricSpace.toPseudoEMetricSpace _
        (@MetricSpace.toEMetricSpace _
          (@NormedAddCommGroup.toMetricSpace _ (sobolevSpace_nacg n m))))
      inferInstance
      (sobolevFourierEquiv n m).toFun := by sorry

/-- Packaging `sobolevFourierEquiv` and its isometry property as an `IsometryEquiv`. -/
def sobolevFourierIsometry (n m : ℕ) :
    (SobolevEmbedding.SobolevSpace n m) ≃ᵢ
      (MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  @IsometryEquiv.mk _ _
    (@EMetricSpace.toPseudoEMetricSpace _
      (@MetricSpace.toEMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _ (sobolevSpace_nacg n m))))
    inferInstance
    (sobolevFourierEquiv n m)
    (sobolevFourierEquiv_isometry n m)


/-- The Fourier-side equivalence sends `0` to `0`. -/
theorem sobolevFourierEquiv_map_zero (n m : ℕ) :
    (sobolevFourierEquiv n m) 0 = 0 := by sorry


/-- The Fourier-side isometry sends `0` to `0`. -/
theorem sobolevFourierIsometry_map_zero (n m : ℕ) :
    sobolevFourierIsometry n m 0 = 0 := by
  simp [sobolevFourierIsometry, IsometryEquiv.coe_mk, sobolevFourierEquiv_map_zero]


/-- The Fourier-side equivalence commutes with multiplication by `Complex.I`. -/
theorem sobolevFourierEquiv_map_I_smul (n m : ℕ)
    (u : SobolevEmbedding.SobolevSpace n m) :
    (sobolevFourierEquiv n m) (Complex.I • u) =
      Complex.I • (sobolevFourierEquiv n m) u := by sorry


/-- The Fourier-side isometry commutes with multiplication by `Complex.I`. -/
theorem sobolevFourierIsometry_map_I_smul (n m : ℕ)
    (u : SobolevEmbedding.SobolevSpace n m) :
    sobolevFourierIsometry n m (Complex.I • u) =
      Complex.I • sobolevFourierIsometry n m u := by
  simp [sobolevFourierIsometry, IsometryEquiv.coe_mk, sobolevFourierEquiv_map_I_smul]

/-- The Fourier-side `ℝ`-linear isometric equivalence `SobolevSpace n m ≃ₗᵢ[ℝ] Lp ℂ 2`. -/
def sobolevFourierLinearIsometry (n m : ℕ) :
    SobolevEmbedding.SobolevSpace n m ≃ₗᵢ[ℝ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (sobolevFourierIsometry n m).toRealLinearIsometryEquivOfMapZero
    (sobolevFourierIsometry_map_zero n m)

/-- The `ℝ`-linear isometry agrees pointwise with the bare isometry. -/
@[simp] lemma sobolevFourierLinearIsometry_apply (n m : ℕ)
    (u : SobolevEmbedding.SobolevSpace n m) :
    sobolevFourierLinearIsometry n m u = sobolevFourierIsometry n m u := by
  simp [sobolevFourierLinearIsometry]


/-- The `ℝ`-linear Fourier isometry commutes with multiplication by `Complex.I`. -/
lemma sobolevFourierLinearIsometry_map_I_smul (n m : ℕ)
    (u : SobolevEmbedding.SobolevSpace n m) :
    sobolevFourierLinearIsometry n m (Complex.I • u) =
      Complex.I • sobolevFourierLinearIsometry n m u := by
  simp only [sobolevFourierLinearIsometry_apply, sobolevFourierIsometry_map_I_smul]


/-- The `ℝ`-linear Fourier isometry is also `ℂ`-linear: it commutes with multiplication by any complex scalar. -/
lemma sobolevFourierLinearIsometry_map_smul (n m : ℕ)
    (c : ℂ) (u : SobolevEmbedding.SobolevSpace n m) :
    sobolevFourierLinearIsometry n m (c • u) =
      c • sobolevFourierLinearIsometry n m u := by
  set T := sobolevFourierLinearIsometry n m
  have hcu : c • u = (↑c.re : ℂ) • u + (↑c.im : ℂ) • (Complex.I • u) := by
    conv_lhs => rw [(Complex.re_add_im c).symm]
    rw [add_smul, mul_smul]
  have h_re : T ((↑c.re : ℂ) • u) = (↑c.re : ℂ) • T u := by
    show T ((c.re : ℝ) • u) = (c.re : ℝ) • T u
    exact map_smul T c.re u
  have h_im : T ((↑c.im : ℂ) • (Complex.I • u)) =
      (↑c.im : ℂ) • (Complex.I • T u) := by
    have h1 : (↑c.im : ℂ) • (Complex.I • u) = (c.im : ℝ) • (Complex.I • u) := rfl
    have h2 : T ((c.im : ℝ) • (Complex.I • u)) = (c.im : ℝ) • T (Complex.I • u) :=
      map_smul T c.im (Complex.I • u)
    rw [h1, h2, sobolevFourierLinearIsometry_map_I_smul]
    rfl
  rw [hcu, map_add, h_re, h_im]
  conv_rhs => rw [(Complex.re_add_im c).symm, add_smul, mul_smul]

/-- The Sobolev inner product on `SobolevSpace n m`, transported from the `L^2` inner product through the Fourier isometry. -/
def sobolevInner {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) : ℂ :=
  @inner ℂ _ _ (sobolevFourierLinearIsometry n m u) (sobolevFourierLinearIsometry n m v)

/-- The complex `Inner` instance on `SobolevSpace n m` given by `sobolevInner`. -/
instance sobolevSpace_inner' (n m : ℕ) :
    Inner ℂ (SobolevEmbedding.SobolevSpace n m) :=
  ⟨fun u v => sobolevInner u v⟩

/-- The Sobolev norm squared equals the real part of `⟨u, u⟩`. -/
theorem sobolevInner_norm_sq {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m) :
    @Norm.norm _ (sobolevSpace_nacg n m).toNorm u ^ 2 =
      Complex.re (sobolevInner u u) := by
  simp only [sobolevInner]
  rw [← (sobolevFourierLinearIsometry n m).norm_map u]
  exact @InnerProductSpace.norm_sq_eq_re_inner ℂ _ _ _ _
    (sobolevFourierLinearIsometry n m u)

/-- Conjugate symmetry: `conj ⟨v, u⟩ = ⟨u, v⟩`. -/
theorem sobolevInner_conj_symm {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) :
    starRingEnd ℂ (sobolevInner v u) = sobolevInner u v := by
  simp only [sobolevInner]
  exact @inner_conj_symm ℂ _ _ _ _
    (sobolevFourierLinearIsometry n m u) (sobolevFourierLinearIsometry n m v)

/-- Additivity of the inner product in the left argument. -/
theorem sobolevInner_add_left {n m : ℕ}
    (u v w : SobolevEmbedding.SobolevSpace n m) :
    sobolevInner (u + v) w = sobolevInner u w + sobolevInner v w := by
  simp only [sobolevInner, map_add]
  exact @inner_add_left ℂ _ _ _ _
    (sobolevFourierLinearIsometry n m u) (sobolevFourierLinearIsometry n m v)
    (sobolevFourierLinearIsometry n m w)

/-- Conjugate-linearity in the left argument: `⟨c • u, v⟩ = conj c * ⟨u, v⟩`. -/
theorem sobolevInner_smul_left {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) (c : ℂ) :
    sobolevInner (c • u) v = starRingEnd ℂ c * sobolevInner u v := by
  simp only [sobolevInner, sobolevFourierLinearIsometry_map_smul]
  exact @inner_smul_left ℂ _ _ _ _
    (sobolevFourierLinearIsometry n m u) (sobolevFourierLinearIsometry n m v) c

/-- The complex inner product space structure on `SobolevSpace n m`. -/
abbrev sobolevSpace_innerProductSpace (n m : ℕ) :
    InnerProductSpace ℂ (SobolevEmbedding.SobolevSpace n m) :=
  @InnerProductSpace.mk ℂ _ _ (sobolevSpace_nacg n m).toSeminormedAddCommGroup
    (sobolevSpace_normedSpace' n m) (sobolevSpace_inner' n m)
    (fun u => sobolevInner_norm_sq u)
    (fun u v => sobolevInner_conj_symm u v)
    (fun u v w => sobolevInner_add_left u v w)
    (fun u v c => sobolevInner_smul_left u v c)

/-- Completeness of `SobolevSpace n m`, inherited via the Fourier isometry with `L^2`. -/
theorem sobolevSpace_completeSpace (n m : ℕ) :
    CompleteSpace (SobolevEmbedding.SobolevSpace n m) :=
  (sobolevFourierIsometry n m).completeSpace


/-- The map sending `u ∈ SobolevSpace n m` to its image in `L^2` via the Fourier isometry. -/
def sobolevSpace_toL2 (n m : ℕ)
    [NormedAddCommGroup (SobolevEmbedding.SobolevSpace n m)]
    (u : SobolevEmbedding.SobolevSpace n m) :
    MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
  letI : NormedAddCommGroup (SobolevEmbedding.SobolevSpace n m) := sobolevSpace_nacg n m
  (sobolevFourierIsometry n m) u


/-- Isometric property of `sobolevSpace_toL2` on differences. -/
theorem sobolevSpace_toL2_norm_sub (n m : ℕ)
    (u v : SobolevEmbedding.SobolevSpace n m) :
    ‖u - v‖ = ‖sobolevSpace_toL2 n m u - sobolevSpace_toL2 n m v‖ := by
  simp only [sobolevSpace_toL2]
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact (IsometryEquiv.dist_eq (sobolevFourierIsometry n m) u v).symm


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- For any Schwartz function `φ` and `j ≤ m`, the iterated derivative of `φ` is in `L^2`. -/
theorem schwartz_iteratedFDeriv_memLp {n m : ℕ}
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j (⇑φ) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  set E := EuclideanSpace ℝ (Fin n)
  set g := fun x : E => iteratedFDeriv ℝ j (⇑φ) x
  have hcont : Continuous g :=
    φ.smooth'.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have htemp : (volume : Measure E).HasTemperateGrowth := inferInstance
  obtain ⟨k, hk⟩ := htemp.exists_eLpNorm_lt_top (p := 2)
  have h_one_add (x : E) : (0 : ℝ) < 1 + ‖x‖ := by positivity
  set B := 2 ^ k * (Finset.Iic (k, j)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) φ
  have hB : ∀ x : E, (1 + ‖x‖) ^ k * ‖g x‖ ≤ B :=
    fun x => SchwartzMap.one_add_le_sup_seminorm_apply (m := (k, j)) le_rfl le_rfl φ x
  have hg_bound : ∀ x : E, ‖g x‖ ≤ B * (1 + ‖x‖) ^ (-(k : ℝ)) := by
    intro x
    have hpow_pos : (0 : ℝ) < (1 + ‖x‖) ^ k := by positivity
    rw [Real.rpow_neg (h_one_add x).le, Real.rpow_natCast,
      mul_comm B, ← div_eq_inv_mul, le_div_iff₀ hpow_pos]
    linarith [hB x]
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  calc eLpNorm g 2 volume
      ≤ eLpNorm (fun x : E => B * (1 + ‖x‖) ^ (-(k : ℝ))) 2 volume :=
        eLpNorm_mono_real hg_bound
    _ < ⊤ := by
        have heq : (fun x : E => B * (1 + ‖x‖) ^ (-(k : ℝ))) =
            B • (fun x : E => (1 + ‖x‖) ^ (-(k : ℝ))) := by
          ext x; simp [Pi.smul_apply, smul_eq_mul]
        rw [heq, eLpNorm_const_smul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hk

/-- Promote a Schwartz function to an element of `SobolevSpace n m`. -/
def schwartzToSobolev (n m : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    SobolevEmbedding.SobolevSpace n m :=
  ⟨⇑φ, φ.smooth m, fun j hj => schwartz_iteratedFDeriv_memLp φ j hj⟩

/-- The underlying function of `schwartzToSobolev n m φ` is `⇑φ`. -/
@[simp] lemma schwartzToSobolev_toFun (n m : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    (schwartzToSobolev n m φ).toFun = ⇑φ := rfl


/-- The Fourier-side equivalence sends the embedded Schwartz function to its `L^2`-class. -/
theorem sobolevFourierEquiv_schwartz (n m : ℕ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    (sobolevFourierEquiv n m) (schwartzToSobolev n m φ) = SchwartzMap.toLp φ 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by sorry


/-- The Fourier isometry sends the embedded Schwartz function to its `L^2`-class. -/
theorem sobolevFourierIsometry_schwartz_toLp (n m : ℕ)
    [NormedAddCommGroup (SobolevEmbedding.SobolevSpace n m)]
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    sobolevSpace_toL2 n m (schwartzToSobolev n m φ) = SchwartzMap.toLp φ 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  simp only [sobolevSpace_toL2, sobolevFourierIsometry, IsometryEquiv.coe_mk]
  exact sobolevFourierEquiv_schwartz n m φ


/-- Existence of a Sobolev representative whose underlying function is `⇑φ` and whose `L^2` image is `SchwartzMap.toLp φ`. -/
theorem sobolevSpace_schwartz_toLp (n m : ℕ)
    [NormedAddCommGroup (SobolevEmbedding.SobolevSpace n m)]
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    ∃ v : SobolevEmbedding.SobolevSpace n m,
      v.toFun = ⇑φ ∧
      sobolevSpace_toL2 n m v = SchwartzMap.toLp φ 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) :=
  ⟨schwartzToSobolev n m φ, schwartzToSobolev_toFun n m φ,
   sobolevFourierIsometry_schwartz_toLp n m φ⟩

open scoped FourierTransform in

/-- Melrose Proposition 9.8: `H^m(ℝⁿ)` is a Hilbert space (Fourier-side isomorphic to `L²`), and its dual is `H^{-m}(ℝⁿ)`. -/
theorem proposition_9_8 (n : ℕ) (m : ℝ) :
    (∃ Φ : SobolevSpace.Hs n m ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      DenseRange (Φ.symm ∘
        (SchwartzMap.toLpCLM ℝ ℂ 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
    Nonempty (SobolevSpace.Hs n (-m) ≃ₗᵢ⋆[ℂ] (SobolevSpace.Hs n m →L[ℂ] ℂ)) :=
  SobolevSpace.proposition_9_8 n m

end SobolevHilbert

end
