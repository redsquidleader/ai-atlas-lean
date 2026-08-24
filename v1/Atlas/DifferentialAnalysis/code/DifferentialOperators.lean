/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Atlas.DifferentialAnalysis.code.DistributionSupport
import Atlas.DifferentialAnalysis.code.SchwartzTranslateContinuity

open scoped SchwartzMap
open TemperedDistribution MvPolynomial

noncomputable section

namespace DifferentialOperators

variable (n : ℕ)

/-- The **principal symbol** of a polynomial `P` of (assumed) order `m`:
the degree-`m` homogeneous component of `P`. -/
def principalSymbol (m : ℕ) (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent m P

/-- Unfolding lemma: `principalSymbol n m P = homogeneousComponent m P`. -/
@[simp]
theorem principalSymbol_def (m : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    principalSymbol n m P = homogeneousComponent m P :=
  rfl

/-- A polynomial `P(ξ)` (of order `m`) is **elliptic** if its principal
symbol `P_m(ξ)` does not vanish for any nonzero real vector `ξ ∈ ℝⁿ`.
(See Melrose, Definition 11.11.) -/
def IsElliptic (m : ℕ) (P : MvPolynomial (Fin n) ℂ) : Prop :=
  ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
    MvPolynomial.eval (fun i => (ξ i : ℂ)) (principalSymbol n m P) ≠ 0

/-- The **Fourier symbol** `P(2πiξ)` of the differential operator `P(D)`,
viewed as a function `ℝⁿ → ℂ`. -/
def polySymbol (P : MvPolynomial (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun ξ => MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) P

/-- The **constant-coefficient differential operator** `P(D)` acting on
tempered distributions, defined as the Fourier multiplier with symbol
`P(2πiξ)`. -/
def constCoeffDiffOp (P : MvPolynomial (Fin n) ℂ) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ (polySymbol n P)

/-- A tempered distribution `E` is a **fundamental solution** of `P(D)`
if `P(D) E = δ₀`. -/
def IsTemperedFundamentalSolution (P : MvPolynomial (Fin n) ℂ)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  constCoeffDiffOp n P E = TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))


/-- **Theorem 11.4 (Melrose).** Every nonzero constant-coefficient differential
operator `P(D)` admits a tempered fundamental solution. -/
theorem constCoeffDiffOp_has_tempered_fundamental_solution
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), IsTemperedFundamentalSolution n P E := by sorry

open Set Function MeasureTheory

section SingularSupport

variable {n : ℕ}

/-- A tempered distribution `u` is **smooth near** a point `x₀` if there
exists an open neighbourhood `U` of `x₀` on which `u` is represented by a
smooth function (under pairing with Schwartz functions supported in `U`). -/
def isSmoothNear (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x₀ ∈ U ∧
    ∃ f : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
        u φ = ∫ y, φ y • f y

/-- The **singular support** of `u`: the set of points `x₀` near which
`u` fails to be smooth. -/
def singularSupport (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x₀ | ¬ isSmoothNear u x₀}

/-- `u` **vanishes on** the set `U` if it sends every test function
supported in `U` to zero. -/
def vanishesOn (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) → u φ = 0

end SingularSupport

section OperatorProperties

variable {n : ℕ}


/-- **Locality of `P(D)`.** If `u` vanishes on the open set `U`, then so
does `P(D) u`. -/
theorem constCoeffDiffOp_local
    (P : MvPolynomial (Fin n) ℂ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hv : vanishesOn u U) : vanishesOn (constCoeffDiffOp n P u) U := by sorry


/-- **Partition of `u`** by a temperate cutoff: for any `χ` of temperate
growth, `χ · u + (1 - χ) · u = u`. -/
theorem smulLeftCLM_add_complement
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : Function.HasTemperateGrowth χ) :
    smulLeftCLM ℂ χ u + smulLeftCLM ℂ (1 - χ) u = u := by
  have h1χ : Function.HasTemperateGrowth (1 - χ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hχ
  ext φ
  simp only [UniformConvergenceCLM.add_apply, smulLeftCLM_apply_apply]
  rw [← map_add u]
  congr 1
  ext x
  simp only [SchwartzMap.add_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hχ, SchwartzMap.smulLeftCLM_apply_apply h1χ]
  simp [Pi.sub_apply, smul_eq_mul, sub_mul, one_mul]

/-- If `χ` is a smooth temperate cutoff supported in an open set `U` on
which `u` is represented by a smooth function `f`, then `χ · u` is
globally smooth — represented by `χ · f`. -/
theorem smulLeft_globally_smooth_of_supported_in_smooth_region
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_supp : ∀ x, x ∉ U → χ x = 0)
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
      u φ = ∫ y, φ y • f y)
    (hχ_temp : Function.HasTemperateGrowth χ) :
    ∀ y : EuclideanSpace ℝ (Fin n), isSmoothNear (smulLeftCLM ℂ χ u) y := by
  intro y


  refine ⟨Set.univ, isOpen_univ, Set.mem_univ y, χ * f, hχ_smooth.mul hf_smooth,
    fun φ _ => ?_⟩
  simp only [smulLeftCLM_apply_apply]


  have hχφ_supp : ∀ z, z ∉ U → (SchwartzMap.smulLeftCLM ℂ χ φ) z = 0 := by
    intro z hz
    simp only [SchwartzMap.smulLeftCLM]
    split
    · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
        ContinuousLinearMap.flip_apply]
      rw [hχ_supp z hz, zero_smul]
    · simp
  rw [hf_eq (SchwartzMap.smulLeftCLM ℂ χ φ) hχφ_supp]
  congr 1; ext z
  simp only [SchwartzMap.smulLeftCLM]
  split
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.flip_apply, Pi.mul_apply]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  · exact absurd hχ_temp ‹_›

/-- If `χ ≡ 1` on the open set `V`, then `(1 - χ) · u` **vanishes** on
`V`. -/
theorem smulLeft_complement_vanishesOn
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (V : Set (EuclideanSpace ℝ (Fin n)))
    (hχ_one : ∀ x ∈ V, χ x = 1)
    (h1χ_temp : Function.HasTemperateGrowth (1 - χ)) :
    vanishesOn (smulLeftCLM ℂ (1 - χ) u) V := by
  intro φ hφ_supp
  simp only [smulLeftCLM_apply_apply]

  suffices h : SchwartzMap.smulLeftCLM ℂ (1 - χ) φ = 0 by rw [h, map_zero]
  ext x
  simp only [SchwartzMap.smulLeftCLM]
  split
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.flip_apply, SchwartzMap.zero_apply]
    by_cases hxV : x ∈ V
    · rw [show (1 - χ) x = 1 - χ x from rfl, hχ_one x hxV, sub_self, zero_smul]
    · rw [hφ_supp x hxV, smul_zero]
  · simp


/-- **Smooth cutoff in an open set.** Around any point `x₀` of an open
set `U`, there is a smooth temperate function `χ` vanishing outside `U`
and equal to `1` on a smaller open neighbourhood of `x₀`. -/
theorem exists_smooth_cutoff_in_open
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ U) :
    ∃ (χ : EuclideanSpace ℝ (Fin n) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      Function.HasTemperateGrowth χ ∧
      (∀ x, x ∉ U → χ x = 0) ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x₀ ∈ V ∧ ∀ x ∈ V, χ x = 1) := by sorry


/-- **Cutoff decomposition near a smooth point.** If `u` is smooth near
`x₀`, then `u = v + w` where `v` is **globally smooth** and `w` vanishes
on an open neighbourhood `U` of `x₀`. -/
theorem cutoff_decomposition
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (x₀ : EuclideanSpace ℝ (Fin n))
    (h : isSmoothNear u x₀) :
    ∃ v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
    ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ x₀ ∈ U ∧
      v + w = u ∧
      (∀ y : EuclideanSpace ℝ (Fin n), isSmoothNear v y) ∧
      vanishesOn w U := by

  obtain ⟨U₀, hU₀_open, hx₀_U₀, f, hf_smooth, hf_eq⟩ := h

  obtain ⟨χ, hχ_smooth, hχ_temp, hχ_supp, V, hV_open, hx₀_V, hχ_one⟩ :=
    exists_smooth_cutoff_in_open U₀ hU₀_open x₀ hx₀_U₀

  set v := smulLeftCLM ℂ χ u
  set w := smulLeftCLM ℂ (1 - χ) u
  have h1χ_temp : Function.HasTemperateGrowth (1 - χ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hχ_temp

  refine ⟨v, w, V, hV_open, hx₀_V, ?_, ?_, ?_⟩

  · exact smulLeftCLM_add_complement χ u hχ_temp

  · exact smulLeft_globally_smooth_of_supported_in_smooth_region χ u U₀ f
      hχ_smooth hχ_supp hf_smooth hf_eq hχ_temp

  · exact smulLeft_complement_vanishesOn χ u V hχ_one h1χ_temp

/-- The sum of a globally smooth distribution `v` and one (`w`) that
vanishes on a neighbourhood `U` of `x₀` is smooth near `x₀`. -/
theorem smooth_plus_vanishing_is_smooth
    (v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hx : x₀ ∈ U)
    (hv : ∀ y : EuclideanSpace ℝ (Fin n), isSmoothNear v y)
    (hw : vanishesOn w U) :
    isSmoothNear (v + w) x₀ := by

  obtain ⟨V, hV_open, hx_V, f, hf_smooth, hv_eq⟩ := hv x₀

  refine ⟨V ∩ U, hV_open.inter hU, ⟨hx_V, hx⟩, f, hf_smooth, ?_⟩
  intro φ hφ_supp

  simp only [UniformConvergenceCLM.add_apply]

  have hφ_V : ∀ y, y ∉ V → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨hyV, _⟩ => hy hyV)
  have hφ_U : ∀ y, y ∉ U → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨_, hyU⟩ => hy hyU)

  rw [hv_eq φ hφ_V]

  rw [hw φ hφ_U, add_zero]

/-- If `u` vanishes on the open set `U`, then `u` is **smooth** at every
point of `U` (with smooth representative `0`). -/
theorem isSmoothNear_of_vanishesOn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hv : vanishesOn u U)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ U) :
    isSmoothNear u x₀ :=
  ⟨U, hU, hx₀, 0, contDiff_const, fun φ hφ => by rw [hv φ hφ]; simp⟩


/-- If `u` is **globally smooth** (represented by a smooth `f`), then
`P(D) u` is also globally smooth — represented by an explicit smooth `g`
(the classical action of `P(D)` on `f`). -/
theorem constCoeffDiffOp_of_global_smooth_rep
    (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (huf : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u φ = ∫ y, φ y • f y) :
     ∃ g : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        constCoeffDiffOp n P u φ = ∫ y, φ y • g y := by sorry

/-- **`P(D)` preserves smoothness at every point.** If `u` is smooth at
every point, then so is `P(D) u`. -/
theorem constCoeffDiffOp_preserves_global_smoothness
    (P : MvPolynomial (Fin n) ℂ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ∀ x₀ : EuclideanSpace ℝ (Fin n), isSmoothNear u x₀) :
    ∀ x₀ : EuclideanSpace ℝ (Fin n), isSmoothNear (constCoeffDiffOp n P u) x₀ := by
  intro x₀
  obtain ⟨U, hU_open, hx₀_U, f, hf_smooth, hf_eq⟩ := h x₀
  obtain ⟨χ, hχ_smooth, hχ_temp, hχ_supp, V, hV_open, hx₀_V, hχ_one⟩ :=
    exists_smooth_cutoff_in_open U hU_open x₀ hx₀_U
  set v := smulLeftCLM ℂ χ u
  set w := smulLeftCLM ℂ (1 - χ) u
  have h1χ_temp : Function.HasTemperateGrowth (1 - χ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hχ_temp
  have hvw : v + w = u := smulLeftCLM_add_complement χ u hχ_temp
  rw [← hvw, map_add]

  have hv_global : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), v φ = ∫ y, φ y • (χ * f) y := by
    intro φ
    show u (SchwartzMap.smulLeftCLM ℂ χ φ) = ∫ y, φ y • (χ * f) y
    have hχφ_supp : ∀ z, z ∉ U → (SchwartzMap.smulLeftCLM ℂ χ φ) z = 0 := by
      intro z hz
      simp only [SchwartzMap.smulLeftCLM]
      split
      · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
          ContinuousLinearMap.flip_apply]
        rw [hχ_supp z hz, zero_smul]
      · simp
    rw [hf_eq (SchwartzMap.smulLeftCLM ℂ χ φ) hχφ_supp]
    congr 1; ext z
    simp only [SchwartzMap.smulLeftCLM]
    split
    · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
        ContinuousLinearMap.flip_apply, Pi.mul_apply]
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]; ring
    · exact absurd hχ_temp ‹_›
  obtain ⟨gv, hgv_smooth, hgv_eq⟩ :=
    constCoeffDiffOp_of_global_smooth_rep P v (χ * f) (hχ_smooth.mul hf_smooth) hv_global
  have hPDv_smooth : ∀ y, isSmoothNear (constCoeffDiffOp n P v) y := fun y =>
    ⟨Set.univ, isOpen_univ, Set.mem_univ y, gv, hgv_smooth, fun φ _ => hgv_eq φ⟩
  have hw_vanish : vanishesOn w V :=
    smulLeft_complement_vanishesOn χ u V hχ_one h1χ_temp
  have hPDw_vanish : vanishesOn (constCoeffDiffOp n P w) V :=
    constCoeffDiffOp_local P w V hV_open hw_vanish
  exact smooth_plus_vanishing_is_smooth
    (constCoeffDiffOp n P v) (constCoeffDiffOp n P w) x₀ V hV_open hx₀_V
    hPDv_smooth hPDw_vanish

end OperatorProperties

section SingularSupportInclusion

variable {n : ℕ}

/-- **Singular support is contracted by `P(D)`:**
`singsupp(P(D) u) ⊆ singsupp u`. -/
theorem singularSupport_apply_subset
    (P : MvPolynomial (Fin n) ℂ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport (constCoeffDiffOp n P u) ⊆ singularSupport u := by
  intro x hx
  unfold singularSupport at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hsmooth_u
  apply hx
  obtain ⟨v, w, U, hU_open, hx_mem, hvw_eq, hv_smooth, hw_vanish⟩ :=
    cutoff_decomposition u x hsmooth_u
  rw [← hvw_eq, map_add]
  exact smooth_plus_vanishing_is_smooth
    (constCoeffDiffOp n P v) (constCoeffDiffOp n P w) x U hU_open hx_mem
    (constCoeffDiffOp_preserves_global_smoothness P v hv_smooth)
    (constCoeffDiffOp_local P w U hU_open hw_vanish)

end SingularSupportInclusion

section WeakConvergence

open Filter Topology

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Scalar multiplication is sequentially weakly continuous in `𝓢'`:
if `u j → u₀`, then `c · u j → c · u₀`. -/
theorem tendsto_const_smul {p : Filter ι} {u : ι → 𝓢'(E, F)} {u₀ : 𝓢'(E, F)}
    (hu : Tendsto u p (𝓝 u₀)) (c : ℂ) :
    Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) :=
  ((continuous_const_smul c).tendsto _).comp hu

/-- Addition is sequentially weakly continuous in `𝓢'`:
if `u j → u₀` and `u' j → u₀'`, then `u j + u' j → u₀ + u₀'`. -/
theorem tendsto_add {p : Filter ι} {u u' : ι → 𝓢'(E, F)} {u₀ u₀' : 𝓢'(E, F)}
    (hu : Tendsto u p (𝓝 u₀)) (hu' : Tendsto u' p (𝓝 u₀')) :
    Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) :=
  hu.add hu'

/-- `P(D)` is sequentially weakly continuous: weakly convergent sequences
of distributions are taken to weakly convergent sequences. -/
theorem tendsto_constCoeffDiffOp {n : ℕ} {p : Filter ι}
    {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (P : MvPolynomial (Fin n) ℂ) :
    Tendsto (fun j => constCoeffDiffOp n P (u j)) p
      (𝓝 (constCoeffDiffOp n P u₀)) :=
  ((constCoeffDiffOp n P).continuous.tendsto _).comp hu

/-- Left multiplication by a function `g` (as a CLM on `𝓢'`) is
sequentially weakly continuous. -/
theorem tendsto_smul_left {p : Filter ι} {u : ι → 𝓢'(E, F)} {u₀ : 𝓢'(E, F)}
    (hu : Tendsto u p (𝓝 u₀)) (g : E → ℂ) :
    Tendsto (fun j => TemperedDistribution.smulLeftCLM F g (u j)) p
      (𝓝 (TemperedDistribution.smulLeftCLM F g u₀)) :=
  ((TemperedDistribution.smulLeftCLM F g).continuous.tendsto _).comp hu

/-- **Combined weak continuity package.** Packaging the four preceding
weak-continuity results into one statement; this is the conjunction
recorded as `proposition_11_2` (Melrose, Proposition 11.2). -/
theorem tendsto_smul_add_diffOp_smulLeft {n : ℕ} {p : Filter ι}
    {u u' : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ u₀' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (hu' : Tendsto u' p (𝓝 u₀'))
    (c : ℂ) (P : MvPolynomial (Fin n) ℂ) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) ∧
    Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) ∧
    Tendsto (fun j => constCoeffDiffOp n P (u j)) p
      (𝓝 (constCoeffDiffOp n P u₀)) ∧
    Tendsto (fun j => TemperedDistribution.smulLeftCLM ℂ g (u j)) p
      (𝓝 (TemperedDistribution.smulLeftCLM ℂ g u₀)) :=
  ⟨tendsto_const_smul hu c, tendsto_add hu hu',
   tendsto_constCoeffDiffOp hu P, tendsto_smul_left hu g⟩

alias proposition_11_2 := tendsto_smul_add_diffOp_smulLeft

end WeakConvergence

section HypoellipticRegularity
open scoped Pointwise

variable {n}

/-- A tempered distribution `F` is a **parametrix** for `P(D)` if
`P(D) F - δ₀` has empty singular support, i.e. it is smooth everywhere.
(See Melrose, Definition 11.8.) -/
def IsParametrix (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  singularSupport
    (constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))) = ∅

/-- `P(D)` is **hypoelliptic** if it admits a parametrix `F` whose
singular support is contained in `{0}`. -/
def IsHypoelliptic (P : MvPolynomial (Fin n) ℂ) : Prop :=
  ∃ (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
    IsParametrix P F ∧
    singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))}


/-- **Existence of a smooth compactly-supported cutoff equal to `1` near
the origin.** Used to localise parametrices near `0`. -/
theorem smooth_cutoff_near_zero_for_parametrix (n : ℕ) :
    ∃ (φ : EuclideanSpace ℝ (Fin n) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      HasCompactSupport φ ∧
      Function.HasTemperateGrowth φ ∧
      (∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧
        (0 : EuclideanSpace ℝ (Fin n)) ∈ U ∧ ∀ x ∈ U, φ x = 1) := by

  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨1, 2, one_pos, one_lt_two⟩

  refine ⟨fun x => (b x : ℂ), ?_, ?_, ?_, ?_⟩
  ·
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  ·
    exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  ·
    exact (b.hasCompactSupport.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  ·
    refine ⟨Metric.ball 0 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_⟩
    intro x hx
    show (b x : ℂ) = 1
    have : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [this]


/-- If `φ` is a smooth compactly-supported temperate function, then
`φ · F` has compact distributional support contained in `tsupport φ`. -/
theorem smulLeft_compactSupp_gives_compact_support
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_temp : Function.HasTemperateGrowth φ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → ψ y = 0) → (TemperedDistribution.smulLeftCLM ℂ φ F) ψ = 0 := by
  refine ⟨tsupport φ, hφ_supp, fun ψ hψ => ?_⟩
  simp only [smulLeftCLM_apply_apply]
  suffices h : SchwartzMap.smulLeftCLM ℂ φ ψ = 0 by rw [h, map_zero]
  ext y
  simp only [SchwartzMap.smulLeftCLM_apply_apply hφ_temp, SchwartzMap.zero_apply]
  by_cases hy : y ∈ tsupport φ
  · rw [hψ y hy, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]


/-- **Singular support contracts under left multiplication:**
`singsupp(φ · F) ⊆ singsupp F` for `φ` a smooth temperate function. -/
theorem singularSupport_smulLeft_subset_of_temperate
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_temp : Function.HasTemperateGrowth φ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport (TemperedDistribution.smulLeftCLM ℂ φ F) ⊆ singularSupport F := by
  intro x₀ hx₀
  simp only [singularSupport, Set.mem_setOf_eq] at hx₀ ⊢
  intro hF_smooth
  apply hx₀
  obtain ⟨U, hU_open, hx₀_U, f, hf_smooth, hf_eq⟩ := hF_smooth
  refine ⟨U, hU_open, hx₀_U, fun y => φ y * f y, hφ_smooth.mul hf_smooth, fun ψ hψ => ?_⟩
  rw [smulLeftCLM_apply_apply]
  have hφψ_supp : ∀ y, y ∉ U → (SchwartzMap.smulLeftCLM ℂ φ ψ) y = 0 := by
    intro y hy
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
    rw [hψ y hy, smul_zero]
  rw [hf_eq _ hφψ_supp]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
  simp only [smul_eq_mul]
  ring


/-- A smooth function `f` that represents the tempered distribution `u` on
an open set `U` necessarily has temperate growth — a consequence of `u`
itself being a tempered distribution and standard local-to-global growth
estimates. -/
theorem smooth_rep_has_temperate_growth_aux
    {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (heq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
      u φ = ∫ y, φ y • f y) :
    f.HasTemperateGrowth := by sorry

/-- The pointwise product `φ · f` of a Schwartz function and a smooth
function `f` of temperate growth is integrable. -/
theorem schwartz_smul_smooth_integrable
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (heq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
      u φ = ∫ y, φ y • f y)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hφ : ∀ y, y ∉ U → φ y = 0) :
    Integrable (fun y => φ y • f y) volume := by

  have hftemp : f.HasTemperateGrowth :=
    smooth_rep_has_temperate_growth_aux u U hU f hf heq

  have heq_fn : (fun y => φ y • f y) = (fun y => f y • φ y) := by
    ext y; simp [smul_eq_mul, mul_comm]
  rw [heq_fn]

  have h2 : (fun y => f y • φ y) = ⇑(SchwartzMap.smulLeftCLM ℂ f φ) := by
    ext y; rw [SchwartzMap.smulLeftCLM_apply_apply hftemp]
  rw [h2]

  exact (SchwartzMap.smulLeftCLM ℂ f φ).integrable


/-- Smoothness near a point is **closed under subtraction**: if `a` and `b`
are smooth near `x₀`, then so is `a - b`. -/
theorem isSmoothNear_sub
    (a b : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (ha : isSmoothNear a x₀) (hb : isSmoothNear b x₀) :
    isSmoothNear (a - b) x₀ := by
  obtain ⟨U₁, hU₁_open, hx₀_U₁, f₁, hf₁_smooth, hf₁_eq⟩ := ha
  obtain ⟨U₂, hU₂_open, hx₀_U₂, f₂, hf₂_smooth, hf₂_eq⟩ := hb
  refine ⟨U₁ ∩ U₂, hU₁_open.inter hU₂_open, ⟨hx₀_U₁, hx₀_U₂⟩, f₁ - f₂,
         hf₁_smooth.sub hf₂_smooth, fun φ hφ => ?_⟩
  have hφ_U₁ : ∀ z, z ∉ U₁ → φ z = 0 := fun z hz =>
    hφ z (fun ⟨h1, _⟩ => hz h1)
  have hφ_U₂ : ∀ z, z ∉ U₂ → φ z = 0 := fun z hz =>
    hφ z (fun ⟨_, h2⟩ => hz h2)
  simp only [UniformConvergenceCLM.sub_apply]
  rw [hf₁_eq φ hφ_U₁, hf₂_eq φ hφ_U₂, ← MeasureTheory.integral_sub
    (schwartz_smul_smooth_integrable a U₁ hU₁_open f₁ hf₁_smooth hf₁_eq φ hφ_U₁)
    (schwartz_smul_smooth_integrable b U₂ hU₂_open f₂ hf₂_smooth hf₂_eq φ hφ_U₂)]
  congr 1; ext z; exact (smul_sub (φ z) (f₁ z) (f₂ z)).symm


/-- If `F` is a parametrix for `P(D)` with singular support `⊆ {0}` and
`φ ≡ 1` on a neighbourhood of `0`, then `φ · F` is **also a parametrix**.
Cutting `F` by `φ` does not destroy the parametrix property — the
"tail" `(1 - φ) · F` is globally smooth. -/
theorem isParametrix_smulLeft_of_eq_one_near_zero
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFsing : singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))})
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_temp : Function.HasTemperateGrowth φ)
    (hφ_one : ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧
      (0 : EuclideanSpace ℝ (Fin n)) ∈ U ∧ ∀ x ∈ U, φ x = 1) :
    IsParametrix P (TemperedDistribution.smulLeftCLM ℂ φ F) := by

  obtain ⟨U, hU_open, h0_U, hφ_eq_one⟩ := hφ_one

  have h1φ_smooth : ContDiff ℝ (⊤ : ℕ∞) (1 - φ) := contDiff_const.sub hφ_smooth
  have h1φ_temp : Function.HasTemperateGrowth (1 - φ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hφ_temp


  have hdecomp : TemperedDistribution.smulLeftCLM ℂ φ F +
      TemperedDistribution.smulLeftCLM ℂ (1 - φ) F = F :=
    smulLeftCLM_add_complement φ F hφ_temp


  have h1φF_sing : singularSupport (TemperedDistribution.smulLeftCLM ℂ (1 - φ) F) ⊆
      {(0 : EuclideanSpace ℝ (Fin n))} :=
    (singularSupport_smulLeft_subset_of_temperate (1 - φ) h1φ_smooth h1φ_temp F).trans hFsing

  have h1φF_vanish : vanishesOn (TemperedDistribution.smulLeftCLM ℂ (1 - φ) F) U :=
    smulLeft_complement_vanishesOn φ F U hφ_eq_one h1φ_temp

  have h1φF_smooth_zero : isSmoothNear (TemperedDistribution.smulLeftCLM ℂ (1 - φ) F)
      (0 : EuclideanSpace ℝ (Fin n)) :=
    isSmoothNear_of_vanishesOn _ U hU_open h1φF_vanish 0 h0_U

  have h1φF_smooth : ∀ x₀ : EuclideanSpace ℝ (Fin n),
      isSmoothNear (TemperedDistribution.smulLeftCLM ℂ (1 - φ) F) x₀ := by
    intro x₀
    by_cases hx₀ : x₀ ∈ singularSupport (TemperedDistribution.smulLeftCLM ℂ (1 - φ) F)
    ·
      have hx₀_eq : x₀ = 0 := Set.mem_singleton_iff.mp (h1φF_sing hx₀)
      rw [hx₀_eq]; exact h1φF_smooth_zero
    ·
      exact not_not.mp (by rwa [singularSupport, Set.mem_setOf_eq] at hx₀)

  have hPD1φF_smooth : ∀ x₀ : EuclideanSpace ℝ (Fin n),
      isSmoothNear (constCoeffDiffOp n P (TemperedDistribution.smulLeftCLM ℂ (1 - φ) F)) x₀ :=
    constCoeffDiffOp_preserves_global_smoothness P _ h1φF_smooth

  unfold IsParametrix
  rw [Set.eq_empty_iff_forall_notMem]
  intro x₀ hx₀
  rw [singularSupport, Set.mem_setOf_eq] at hx₀
  apply hx₀


  set PDφF := constCoeffDiffOp n P (TemperedDistribution.smulLeftCLM ℂ φ F)
  set PD1φF := constCoeffDiffOp n P (TemperedDistribution.smulLeftCLM ℂ (1 - φ) F)
  set PDF := constCoeffDiffOp n P F
  set δ := TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  have hPD_add : PDφF + PD1φF = PDF := by
    show (constCoeffDiffOp n P) _ + (constCoeffDiffOp n P) _ = (constCoeffDiffOp n P) _
    rw [← map_add]
    exact congr_arg _ hdecomp
  have hkey : PDφF - δ = (PDF - δ) - PD1φF := by
    have h := eq_sub_of_add_eq hPD_add
    rw [h]; abel
  rw [hkey]

  have hPDF_δ_smooth : ∀ x, isSmoothNear (PDF - δ) x := by
    intro x
    by_contra h
    have : x ∈ singularSupport (PDF - δ) := h
    rw [hFparam] at this
    exact this
  exact isSmoothNear_sub (PDF - δ) PD1φF x₀ (hPDF_δ_smooth x₀) (hPD1φF_smooth x₀)

/-- **Compact support arrangement.** Any parametrix with singular support
in `{0}` can be replaced by a parametrix `F'` of *compact distributional
support* (and unchanged singular support). Achieved by multiplying with a
smooth compactly-supported cutoff `φ` that equals `1` near `0`. -/
theorem parametrix_compact_support_arrangement
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFsing : singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))}) :
    ∃ F' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      IsParametrix P F' ∧
      singularSupport F' ⊆ {(0 : EuclideanSpace ℝ (Fin n))} ∧
      (∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          (∀ y, y ∈ K → φ y = 0) → F' φ = 0) := by

  obtain ⟨φ, hφ_smooth, hφ_supp, hφ_temp, hφ_one⟩ :=
    smooth_cutoff_near_zero_for_parametrix n

  refine ⟨TemperedDistribution.smulLeftCLM ℂ φ F, ?_, ?_, ?_⟩

  · exact isParametrix_smulLeft_of_eq_one_near_zero P F hFparam hFsing φ
      hφ_smooth hφ_supp hφ_temp hφ_one

  · exact (singularSupport_smulLeft_subset_of_temperate φ hφ_smooth hφ_temp F).trans hFsing

  · exact smulLeft_compactSupp_gives_compact_support φ hφ_smooth hφ_supp hφ_temp F


/-- **Smooth-remainder splitting.** For any `u`, the parametrix identity
gives a decomposition `u = v + w` with `v = P(D) F - δ₀ ∗ … = ψ` globally
smooth (when `F` has compact d-support and is a parametrix). -/
theorem parametrix_smooth_remainder_exists
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      v + w = u ∧
      (∀ y, isSmoothNear v y) := by

  set ψ := constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  have hψ_smooth : ∀ y, isSmoothNear ψ y := by
    intro y
    rw [IsParametrix, singularSupport] at hFparam
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not] at hFparam
    exact hFparam y
  exact ⟨ψ, u - ψ, by abel, hψ_smooth⟩


/-- **Pseudolocal estimate (distributional convolution form).** For any
parametrix `F` with compact d-support, the singular support of `u` is
contained in `singsupp F + singsupp(P(D) u)`. -/
theorem parametrix_singSupp_u_bound_distribIdentity
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport u ⊆
      singularSupport F + singularSupport (constCoeffDiffOp n P u) := by sorry


/-- **Subtracted-identity version of the pseudolocal estimate.** Removing
the smooth remainder `ψ = P(D)F - δ₀`, the singular support of `u - ψ`
satisfies the same convolution bound. -/
theorem parametrix_identity_distribConvolution_bound
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport (u - (constCoeffDiffOp n P F -
      TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) ⊆
      singularSupport F + singularSupport (constCoeffDiffOp n P u) := by

  set ψ := constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))

  have hψ_smooth : ∀ y, isSmoothNear ψ y := by
    intro y
    rw [IsParametrix, singularSupport] at hFparam
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not] at hFparam
    exact hFparam y


  have h_sub_smooth : singularSupport (u - ψ) ⊆ singularSupport u := by
    intro x hx
    simp only [singularSupport, Set.mem_setOf_eq] at hx ⊢
    intro hu_smooth
    exact hx (isSmoothNear_sub u ψ x hu_smooth (hψ_smooth x))

  exact h_sub_smooth.trans (parametrix_singSupp_u_bound_distribIdentity P F hFparam hFcs u)


/-- **Parametrix singular support bound.** For a parametrix `F` with
compact d-support, `singsupp u ⊆ singsupp F + singsupp(P(D) u)`. -/
theorem parametrix_singSupp_bound
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport u ⊆ singularSupport F + singularSupport (constCoeffDiffOp n P u) := by

  set ψ := constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  have hψ_smooth : ∀ y, isSmoothNear ψ y := by
    intro y
    rw [IsParametrix, singularSupport] at hFparam
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not] at hFparam
    exact hFparam y


  have h_subset : singularSupport u ⊆ singularSupport (u - ψ) := by
    intro x hx
    simp only [singularSupport, Set.mem_setOf_eq] at hx ⊢
    intro h_sub_smooth
    apply hx
    have h_neg_ψ_smooth : isSmoothNear (-ψ) x := by
      obtain ⟨U, hU_open, hx_U, f, hf_smooth, hf_eq⟩ := hψ_smooth x
      exact ⟨U, hU_open, hx_U, -f, hf_smooth.neg, fun φ hφ => by
        simp only [UniformConvergenceCLM.neg_apply]
        rw [hf_eq φ hφ]
        simp [MeasureTheory.integral_neg]⟩
    have h_eq : u = (u - ψ) - (-ψ) := by abel
    rw [h_eq]
    exact isSmoothNear_sub (u - ψ) (-ψ) x h_sub_smooth h_neg_ψ_smooth


  exact h_subset.trans (parametrix_identity_distribConvolution_bound P F hFparam hFcs u)


/-- **Singular support bound for the remainder.** Splitting `u = v + w`
with `v` globally smooth, the singular support of `w` is bounded by
`singsupp F + singsupp(P(D) u)`. -/
theorem parametrix_convolution_singSupp_bound
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hvw : v + w = u)
    (hv_smooth : ∀ y, isSmoothNear v y) :
    singularSupport w ⊆ singularSupport F + singularSupport (constCoeffDiffOp n P u) := by

  have hw_eq : w = u - v := by
    have h : v + w - v = u - v := congrArg (· - v) hvw
    simp only [add_sub_cancel_left] at h
    exact h


  have h_ss_wu : singularSupport w ⊆ singularSupport u := by
    intro x hx
    unfold singularSupport at hx ⊢
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro hu_smooth
    exact hx (hw_eq ▸ isSmoothNear_sub u v x hu_smooth (hv_smooth x))

  exact h_ss_wu.trans (parametrix_singSupp_bound P F hFparam hFcs u)

/-- **Parametrix convolution identity** assembled from the previous
lemmas: there is a smooth-plus-remainder decomposition `u = v + w` such
that `singsupp w ⊆ singsupp F + singsupp(P(D) u)`. -/
theorem parametrix_convolution_identity
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFsing : singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))})
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      v + w = u ∧
      (∀ y, isSmoothNear v y) ∧
      singularSupport w ⊆ singularSupport F + singularSupport (constCoeffDiffOp n P u) := by

  obtain ⟨v, w, hvw, hv_smooth⟩ := parametrix_smooth_remainder_exists P F hFparam hFcs u

  have hw_ss := parametrix_convolution_singSupp_bound P F hFparam hFcs u v w hvw hv_smooth
  exact ⟨v, w, hvw, hv_smooth, hw_ss⟩

/-- **Parametrix inversion (pointwise).** If `P(D)` has a parametrix `F`
with singular support `⊆ {0}`, then for any `u` and any point `x`, if
`P(D) u` is smooth near `x`, so is `u`. -/
theorem parametrix_inversion_isSmoothNear
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFsing : singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))})
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (x : EuclideanSpace ℝ (Fin n))
    (hPu : isSmoothNear (constCoeffDiffOp n P u) x) :
    isSmoothNear u x := by

  obtain ⟨F', hF'param, hF'sing, hF'cs⟩ :=
    parametrix_compact_support_arrangement P F hFparam hFsing

  obtain ⟨v, w, hvw_eq, hv_smooth, hw_ss⟩ :=
    parametrix_convolution_identity P F' hF'param hF'sing hF'cs u

  have hx_not_ss_Pu : x ∉ singularSupport (constCoeffDiffOp n P u) :=
    fun h => h hPu
  have hx_not_ss_w : x ∉ singularSupport w := by
    intro hx_w
    have hx_sum := hw_ss hx_w
    rw [Set.mem_add] at hx_sum
    obtain ⟨a, ha, b, hb, hab⟩ := hx_sum
    have ha0 : a = 0 := Set.mem_singleton_iff.mp (hF'sing ha)
    rw [ha0, zero_add] at hab
    exact hx_not_ss_Pu (hab ▸ hb)

  have hw_smooth_x : isSmoothNear w x := not_not.mp hx_not_ss_w
  obtain ⟨w_v, w_w, W, hW_open, hx_W, hwvw_eq, hw_v_smooth, hw_w_vanish⟩ :=
    cutoff_decomposition w x hw_smooth_x

  rw [← hvw_eq, ← hwvw_eq, show v + (w_v + w_w) = (v + w_v) + w_w from by abel]

  apply smooth_plus_vanishing_is_smooth (v + w_v) w_w x W hW_open hx_W _ hw_w_vanish

  intro y
  obtain ⟨Uv, hUv_open, hy_Uv, fv, hfv_smooth, hfv_eq⟩ := hv_smooth y
  obtain ⟨Uw, hUw_open, hy_Uw, fw, hfw_smooth, hfw_eq⟩ := hw_v_smooth y
  refine ⟨Uv ∩ Uw, hUv_open.inter hUw_open, ⟨hy_Uv, hy_Uw⟩, fv + fw,
         hfv_smooth.add hfw_smooth, fun φ hφ => ?_⟩
  have hφ_Uv : ∀ z, z ∉ Uv → φ z = 0 := fun z hz =>
    hφ z (fun ⟨h1, _⟩ => hz h1)
  have hφ_Uw : ∀ z, z ∉ Uw → φ z = 0 := fun z hz =>
    hφ z (fun ⟨_, h2⟩ => hz h2)
  simp only [UniformConvergenceCLM.add_apply]
  rw [hfv_eq φ hφ_Uv, hfw_eq φ hφ_Uw, ← MeasureTheory.integral_add
    (schwartz_smul_smooth_integrable v Uv hUv_open fv hfv_smooth hfv_eq φ hφ_Uv)
    (schwartz_smul_smooth_integrable w_v Uw hUw_open fw hfw_smooth hfw_eq φ hφ_Uw)]
  congr 1; ext z; exact (smul_add (φ z) (fv z) (fw z)).symm

/-- **Theorem 11.9 (Melrose), easy direction.** If `P(D)` is hypoelliptic
then for any tempered distribution `u`, `singsupp u ⊆ singsupp (P(D) u)`:
wherever `P(D) u` is smooth, so is `u`. -/
theorem singSupp_u_subset_singSupp_PDu_of_hypoelliptic
    (P : MvPolynomial (Fin n) ℂ)
    (hP : IsHypoelliptic P)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport u ⊆ singularSupport (constCoeffDiffOp n P u) := by
  intro x hx hPu_smooth
  obtain ⟨F, hFparam, hFsing⟩ := hP
  exact hx (parametrix_inversion_isSmoothNear P F hFparam hFsing u x hPu_smooth)

/-- **Theorem 11.9 (Melrose).** For a hypoelliptic operator `P(D)`,
`singsupp u = singsupp (P(D) u)`. Combining the inclusion
`singsupp (P(D) u) ⊆ singsupp u` (always true) with the parametrix-based
reverse inclusion. -/
theorem singSupp_eq_of_hypoelliptic
    (P : MvPolynomial (Fin n) ℂ)
    (hP : IsHypoelliptic P)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport u = singularSupport (constCoeffDiffOp n P u) := by
  apply Set.Subset.antisymm
  · exact singSupp_u_subset_singSupp_PDu_of_hypoelliptic P hP u
  · exact singularSupport_apply_subset P u

end HypoellipticRegularity

section EllipticHypoelliptic

variable {n}


/-- **Inverse Fourier transform of a temperate-growth symbol** exists as a
temperate-growth function `F` such that pairing `Q` with `φ̌` equals pairing
`F` with `φ`. (Auxiliary input to the Plancherel argument.) -/
theorem temperateGrowth_inverseFT_exists
    {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ : Function.HasTemperateGrowth Q) :
    ∃ (F : EuclideanSpace ℝ (Fin n) → ℂ), Function.HasTemperateGrowth F ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        ∫ ξ, Q ξ • (FourierTransformInv.fourierInv φ : EuclideanSpace ℝ (Fin n) → ℂ) ξ =
          ∫ y, φ y • F y := by sorry


/-- Auxiliary: any `Cᵏ` function that agrees with `F` away from a small
ball around `0` exists — in fact `F` itself is `Cᵏ` and the conclusion is
trivial in this formulation. -/
theorem temperateGrowth_inverseFT_contDiff_away
    {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ : Function.HasTemperateGrowth Q)
    (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF_tg : Function.HasTemperateGrowth F)
    (hF_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        ∫ ξ, Q ξ • (FourierTransformInv.fourierInv φ : EuclideanSpace ℝ (Fin n) → ℂ) ξ =
          ∫ y, φ y • F y)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ k g ∧
      ∀ y, ε / 2 < ‖y‖ → g y = F y :=


  ⟨F, hF_tg.1.of_le (by exact_mod_cast le_top), fun _ _ => rfl⟩

/-- **Plancherel/Sobolev step.** For any `k`, there is a `Cᵏ` function `g`
representing the inverse Fourier transform of `Q` whenever paired with
Schwartz functions whose Fourier transform vanishes near the origin. -/
theorem temperateGrowth_inverseFT_Ck_representative
    {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ : Function.HasTemperateGrowth Q)
    (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ k g ∧
      ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, ‖y‖ ≤ ε →
          (FourierTransform.fourier (⇑ψ) : EuclideanSpace ℝ (Fin n) → ℂ) y = 0) →
          ∫ ξ, Q ξ • (ψ : EuclideanSpace ℝ (Fin n) → ℂ) ξ =
            ∫ y, (FourierTransform.fourier (⇑ψ) : EuclideanSpace ℝ (Fin n) → ℂ) y • g y := by

  obtain ⟨F, hF_tg, hF_eq⟩ := temperateGrowth_inverseFT_exists Q hQ

  obtain ⟨g, hg_smooth, hg_eq⟩ :=
    temperateGrowth_inverseFT_contDiff_away Q hQ F hF_tg hF_eq k ε hε

  refine ⟨g, hg_smooth, fun ψ hψ_vanish => ?_⟩


  have h_inv : (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =
      (FourierTransformInv.fourierInv (FourierTransform.fourier ψ) :
        EuclideanSpace ℝ (Fin n) → ℂ) :=
    funext fun x => (SchwartzMap.ext_iff.mp
      (FourierTransform.fourierInv_fourier_eq
        (E := 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ψ).symm) x
  rw [h_inv, hF_eq (FourierTransform.fourier ψ)]

  simp_rw [show (⇑(FourierTransformInv.fourierInv (FourierTransform.fourier ψ)) :
      EuclideanSpace ℝ (Fin n) → ℂ) = (ψ : EuclideanSpace ℝ (Fin n) → ℂ) from h_inv.symm,
    ← SchwartzMap.fourier_coe ψ]

  congr 1; ext y
  by_cases hy : ‖y‖ ≤ ε
  · have hv : (FourierTransform.fourier ψ :
        𝓢(EuclideanSpace ℝ (Fin n), ℂ)) y = 0 := by
      have h0 := hψ_vanish y hy; rwa [← SchwartzMap.fourier_coe] at h0
    simp [hv]
  · push_neg at hy
    congr 1; exact (hg_eq y (by linarith : ε / 2 < ‖y‖)).symm

set_option maxHeartbeats 400000 in

/-- **Plancherel / local Sobolev regularity.** The Fourier multiplier
`Q · δ₀` is represented, against Schwartz functions vanishing on a
neighbourhood of `0`, by a `Cᵏ` function `g`. -/
theorem plancherel_sobolev_Ck_away_from_origin
    {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ : Function.HasTemperateGrowth Q)
    (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ k g ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, ‖y‖ ≤ ε → φ y = 0) →
          (TemperedDistribution.fourierMultiplierCLM ℂ Q
            (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) φ =
            ∫ y, φ y • g y := by

  obtain ⟨g, hg_smooth, hg_eq⟩ := temperateGrowth_inverseFT_Ck_representative Q hQ k ε hε
  refine ⟨g, hg_smooth, fun φ hφ_vanish => ?_⟩


  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply, TemperedDistribution.delta_apply,
    SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]

  have heq_int : ∫ ξ, (SchwartzMap.smulLeftCLM ℂ Q (FourierTransformInv.fourierInv φ)) ξ =
      ∫ ξ, Q ξ • (FourierTransformInv.fourierInv φ : EuclideanSpace ℝ (Fin n) → ℂ) ξ := by
    congr 1; ext ξ; exact SchwartzMap.smulLeftCLM_apply_apply hQ _ ξ
  rw [heq_int]


  have hψ_cond : ∀ y, ‖y‖ ≤ ε →
      (FourierTransform.fourier (⇑(FourierTransformInv.fourierInv φ)) :
        EuclideanSpace ℝ (Fin n) → ℂ) y = 0 := by
    intro y hy
    rw [← SchwartzMap.fourier_coe (FourierTransformInv.fourierInv φ)]
    rw [show (FourierTransform.fourier (FourierTransformInv.fourierInv φ) :
        𝓢(EuclideanSpace ℝ (Fin n), ℂ)) = φ from FourierTransform.fourier_fourierInv_eq φ]
    exact hφ_vanish y hy
  rw [hg_eq (FourierTransformInv.fourierInv φ) hψ_cond]

  congr 1; ext y; congr 1
  rw [← SchwartzMap.fourier_coe (FourierTransformInv.fourierInv φ)]
  rw [show (FourierTransform.fourier (FourierTransformInv.fourierInv φ) :
      𝓢(EuclideanSpace ℝ (Fin n), ℂ)) = φ from FourierTransform.fourier_fourierInv_eq φ]


/-- **Fundamental lemma of the calculus of variations** (distributional
form). Two continuous functions agreeing distributionally against all
Schwartz test functions supported in an open set `U` agree pointwise on
`U`. -/
theorem schwartz_distributional_uniqueness_on_open
    {n : ℕ}
    (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U)
    (h : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
      ∫ y, φ y • f₁ y = ∫ y, φ y • f₂ y) :
    Set.EqOn f₁ f₂ U := by sorry


/-- **Whitney-type extension.** A function smooth on an open set `U`
extends to a globally smooth function on `ℝⁿ` agreeing with the original
on `U`. -/
theorem contDiffOn_top_extension_from_open
    {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ (⊤ : ℕ∞) g ∧ Set.EqOn g f U := by sorry

/-- A distribution `T` represented by a `Cᵏ` function on `U` for every
`k ∈ ℕ` is in fact represented by a `C^∞` function on `U`. -/
theorem distribution_smooth_from_all_Ck
    {n : ℕ}
    (T : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U)
    (hCk : ∀ k : ℕ, ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ k g ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
        T φ = ∫ y, φ y • g y) :
    ∃ (f : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
        T φ = ∫ y, φ y • f y := by
  choose g hg_smooth hg_eq using hCk

  have heq : ∀ k : ℕ, Set.EqOn (g k) (g 0) U := by
    intro k
    apply schwartz_distributional_uniqueness_on_open _ _
      (hg_smooth k).continuous (hg_smooth 0).continuous U hU
    intro φ hφ
    exact (hg_eq k φ hφ).symm.trans (hg_eq 0 φ hφ)

  have hg0_smooth_on_U : ContDiffOn ℝ (⊤ : ℕ∞) (g 0) U := by
    rw [contDiffOn_infty]
    intro k
    exact ((hg_smooth k).contDiffOn).congr (fun x hx => (heq k hx).symm)

  obtain ⟨f, hf_smooth, hf_eq_on⟩ :=
    contDiffOn_top_extension_from_open (g 0) U hU hg0_smooth_on_U

  refine ⟨f, hf_smooth, fun φ hφ => ?_⟩
  have h1 : T φ = ∫ y, φ y • g 0 y := hg_eq 0 φ hφ
  have h2 : ∫ y, φ y • g 0 y = ∫ y, φ y • f y := by
    congr 1; ext y
    by_cases hy : y ∈ U
    · rw [hf_eq_on hy]
    · simp [hφ y (fun h => hy h)]
  exact h1.trans h2

/-- **Local smoothness of `Q · δ₀` away from `0`.** If `Q` has temperate
growth, then `Q · δ₀` is represented by a smooth function on a small open
neighbourhood of any nonzero point `x₀`. -/
theorem temperateGrowth_fourierMultiplier_delta_localSmooth
    {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ_temp : Function.HasTemperateGrowth Q)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ≠ 0) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin n))), IsOpen U ∧ x₀ ∈ U ∧
      ∃ (f : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f ∧
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
          (TemperedDistribution.fourierMultiplierCLM ℂ Q
            (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) φ =
            ∫ y, φ y • f y := by

  have hpos : (0 : ℝ) < ‖x₀‖ := norm_pos_iff.mpr hx₀
  set r := ‖x₀‖ / 4 with hr_def
  have hr_pos : 0 < r := by linarith
  set U := Metric.ball x₀ r
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hx₀_mem : x₀ ∈ U := Metric.mem_ball_self hr_pos

  set ε := ‖x₀‖ / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hU_norm_bound : ∀ y ∈ U, ε < ‖y‖ := by
    intro y hy
    rw [Metric.mem_ball, dist_comm] at hy
    have h1 : ‖x₀‖ - r ≤ ‖y‖ := by
      have := norm_sub_norm_le x₀ y
      have h2 : ‖x₀ - y‖ = dist x₀ y := rfl
      linarith
    linarith


  have hCk : ∀ k : ℕ, ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ k g ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
        (TemperedDistribution.fourierMultiplierCLM ℂ Q
          (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) φ =
          ∫ y, φ y • g y := by
    intro k
    obtain ⟨g, hg_smooth, hg_eq⟩ := plancherel_sobolev_Ck_away_from_origin Q hQ_temp k ε hε_pos
    refine ⟨g, hg_smooth, fun φ hφ_supp => hg_eq φ (fun y hy_norm => ?_)⟩
    apply hφ_supp
    intro hy_mem
    exact absurd (hU_norm_bound y hy_mem) (not_lt.mpr hy_norm)

  obtain ⟨f, hf_smooth, hf_eq⟩ := distribution_smooth_from_all_Ck
    (TemperedDistribution.fourierMultiplierCLM ℂ Q
      (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))))
    U hU_open hCk
  exact ⟨U, hU_open, hx₀_mem, f, hf_smooth, hf_eq⟩

/-- **Elliptic parametrix is smooth away from the origin.** If `P` is
elliptic and `Q` is a temperate-growth symbol, then the distribution
`Q · δ₀` is smooth near every nonzero point — a key step in constructing
the parametrix used to prove ellipticity implies hypoellipticity. -/
theorem elliptic_parametrix_smooth_away_from_origin
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (_hP : IsElliptic n m P) (_hn : 0 < n)
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ_temp : Function.HasTemperateGrowth Q) :
    ∀ x₀ : EuclideanSpace ℝ (Fin n), x₀ ≠ 0 →
      isSmoothNear
        (TemperedDistribution.fourierMultiplierCLM ℂ Q
          (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀ := by
  intro x₀ hx₀
  exact temperateGrowth_fourierMultiplier_delta_localSmooth Q hQ_temp x₀ hx₀


/-- **Dominance of the principal symbol.** For an elliptic polynomial `P`
of order `m`, there is a radius `R` past which the contribution of the
lower-order terms `P - P_m` to the Fourier symbol is dominated in norm by
the principal-symbol contribution. -/
theorem polySymbol_principal_dominates
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ R : ℝ, 0 < R ∧ ∀ ξ : EuclideanSpace ℝ (Fin n), R < ‖ξ‖ →
      ‖MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ))
        (P - homogeneousComponent m P)‖ <
      ‖MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ))
        (homogeneousComponent m P)‖ := by sorry

/-- **Non-vanishing of the symbol at large frequencies.** A corollary of
principal-symbol dominance: for an elliptic `P` there is `R > 0` such that
`P(2πiξ) ≠ 0` whenever `‖ξ‖ > R`. -/
theorem polySymbol_ne_zero_of_large_norm
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ R : ℝ, 0 < R ∧ ∀ ξ : EuclideanSpace ℝ (Fin n), R < ‖ξ‖ → polySymbol n P ξ ≠ 0 := by
  obtain ⟨R, hR_pos, hR_dom⟩ := polySymbol_principal_dominates P hP hn
  refine ⟨R, hR_pos, fun ξ hξ heq => ?_⟩
  have hdom := hR_dom ξ hξ

  have hdecomp : polySymbol n P ξ =
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) (homogeneousComponent m P) +
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ))
        (P - homogeneousComponent m P) := by
    simp [polySymbol, map_sub]

  have hab : MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ))
      (homogeneousComponent m P) +
    MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ))
      (P - homogeneousComponent m P) = 0 := by rw [← hdecomp, heq]
  have hprinc_eq := eq_neg_of_add_eq_zero_left hab

  have hnorm_eq : ‖MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ))
      (homogeneousComponent m P)‖ =
    ‖MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ))
        (P - homogeneousComponent m P)‖ := by
    rw [hprinc_eq, norm_neg]

  linarith

/-- **Existence of an elliptic parametrix cutoff function.** For an
elliptic polynomial `P`, there is a smooth compactly-supported cutoff
`φ : ℝⁿ → ℂ` which equals `1` on a neighbourhood of the (compact) zero set
of the Fourier symbol of `P`. The function `1 - φ` then vanishes near the
zeros of `P̂` and allows us to invert `P̂` everywhere modulo a smooth
remainder. -/
theorem elliptic_parametrix_cutoff_exists_aux
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ (φ : EuclideanSpace ℝ (Fin n) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      HasCompactSupport φ ∧
      (∀ ξ : EuclideanSpace ℝ (Fin n),
        polySymbol n P ξ ≠ 0 ∨ φ ξ = 1) ∧
      (∀ ξ : EuclideanSpace ℝ (Fin n),
        polySymbol n P ξ = 0 → ∀ᶠ η in nhds ξ, φ η = 1) := by

  obtain ⟨R, hR_pos, hR_bound⟩ := polySymbol_ne_zero_of_large_norm P hP hn


  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨R + 1, R + 2, by linarith, by linarith⟩

  refine ⟨fun ξ => (b ξ : ℂ), ?_, ?_, ?_, ?_⟩
  ·
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  ·
    exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  ·
    intro ξ
    by_cases hξ : R < ‖ξ‖
    ·
      exact Or.inl (hR_bound ξ hξ)
    ·
      right
      push_neg at hξ
      have h_mem : ξ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        linarith
      simp only [Complex.ofReal_eq_one]
      exact b.one_of_mem_closedBall h_mem
  ·


    intro ξ hξ_zero
    have hξ_norm : ‖ξ‖ ≤ R := by
      by_contra h
      push_neg at h
      exact absurd hξ_zero (hR_bound ξ h)


    have h_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + 1) ∈ nhds ξ := by
      apply Metric.isOpen_ball.mem_nhds
      rw [Metric.mem_ball, dist_zero_right]
      linarith

    filter_upwards [h_ball] with η hη
    simp only [Complex.ofReal_eq_one]
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hη)


/-- **Smoothness of the Fourier symbol.** The map
`ξ ↦ P(2πiξ) : ℝⁿ → ℂ` is `C^∞`. -/
theorem polySymbol_contDiff (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (polySymbol n P) := by
  suffices h : ∀ Q : MvPolynomial (Fin n) ℂ,
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) Q) from h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) =>
        2 * ↑Real.pi * Complex.I * (ξ j : ℂ)) := by
      have hx : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) := by
        have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) =
          (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ (EuclideanSpace.proj j) := by
          ext ξ; simp [EuclideanSpace.proj, Complex.ofRealCLM]
        rw [heq]
        exact Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.contDiff _)
      exact contDiff_const.mul hx
    exact hP.mul hcoord


/-- **Smoothness of the parametrix symbol at zeros of `P̂`.** At a point
`ξ₀` where the Fourier symbol of `P` vanishes (and where the cutoff `φ`
equals `1` on a neighbourhood), the regularised symbol
`(1 - φ(ξ)) · P̂(ξ)⁻¹` is smooth — locally it is identically zero. -/
theorem contDiffAt_parametrix_symbol_at_zero
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_eq_one : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ ≠ 0 ∨ φ ξ = 1)
    (hφ_nhd_zero : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ = 0 → ∀ᶠ η in nhds ξ, φ η = 1)
    (ξ₀ : EuclideanSpace ℝ (Fin n))
    (h_zero : polySymbol n P ξ₀ = 0)
    (h_phi : φ ξ₀ = 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹) ξ₀ := by

  have heq : (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹) =ᶠ[nhds ξ₀] (fun _ => (0 : ℂ)) := by
    filter_upwards [hφ_nhd_zero ξ₀ h_zero] with ξ hξ
    simp [hξ]
  exact contDiffAt_const.congr_of_eventuallyEq heq


/-- **Uniform bound on derivatives of `1/P̂` at infinity.** For an elliptic
polynomial `P`, every derivative of order `k` of the reciprocal symbol
`ξ ↦ 1/P̂(ξ)` is bounded uniformly on `{‖ξ‖ > R}` for some `R > 0`. -/
theorem iteratedFDeriv_inv_polySymbol_bounded
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n) (k : ℕ) :
    ∃ (R : ℝ) (C : ℝ), 0 < R ∧ ∀ ξ : EuclideanSpace ℝ (Fin n), R < ‖ξ‖ →
      ‖iteratedFDeriv ℝ k (fun ξ' => (polySymbol n P ξ')⁻¹) ξ‖ ≤ C := by sorry


/-- **Polynomial bound on derivatives of the parametrix symbol.** Each
iterated derivative of the regularised symbol
`(1 - φ(ξ)) · P̂(ξ)⁻¹` is bounded by `C · (1 + ‖ξ‖)^N` for some `N` and
`C`, witnessing its temperate growth. -/
theorem parametrix_symbol_iteratedFDeriv_bound
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_eq_one : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ ≠ 0 ∨ φ ξ = 1)
    (hφ_nhd_zero : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ = 0 → ∀ᶠ η in nhds ξ, φ η = 1)
    (k : ℕ) :
    ∃ (N : ℕ) (C : ℝ), ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ k (fun ξ' => (1 - φ ξ') * (polySymbol n P ξ')⁻¹) ξ‖ ≤
        C * (1 + ‖ξ‖) ^ N := by

  have hQ_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro ξ₀
    rcases hφ_eq_one ξ₀ with hP_ne | hφ_one
    · exact (contDiffAt_const.sub hφ_smooth.contDiffAt).mul
        ((polySymbol_contDiff n P).contDiffAt.inv hP_ne)
    · by_cases h : polySymbol n P ξ₀ ≠ 0
      · exact (contDiffAt_const.sub hφ_smooth.contDiffAt).mul
          ((polySymbol_contDiff n P).contDiffAt.inv h)
      · push_neg at h
        exact contDiffAt_parametrix_symbol_at_zero P hP hn φ hφ_smooth hφ_supp hφ_eq_one
          hφ_nhd_zero ξ₀ h hφ_one

  have hQ_iter_cont : Continuous (iteratedFDeriv ℝ k
      (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹)) :=
    hQ_smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)

  obtain ⟨R₁, C_out, hR₁_pos, hC_out⟩ := iteratedFDeriv_inv_polySymbol_bounded P hP hn k

  obtain ⟨R₂, hR₂⟩ := hφ_supp.isBounded.subset_ball 0

  set R := max R₁ R₂ + 1
  have hball_compact : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    isCompact_closedBall 0 R
  obtain ⟨C_in, hC_in⟩ := hball_compact.exists_bound_of_continuousOn
    hQ_iter_cont.continuousOn


  have hQ_eq_outside : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ∉ Metric.closedBall 0 R →
      iteratedFDeriv ℝ k (fun ξ' => (1 - φ ξ') * (polySymbol n P ξ')⁻¹) ξ =
      iteratedFDeriv ℝ k (fun ξ' => (polySymbol n P ξ')⁻¹) ξ := by
    intro ξ hξ
    have hξ_not_supp : ξ ∉ tsupport φ := by
      intro h_in
      have := hR₂ h_in
      simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at this hξ
      linarith [le_max_right R₁ R₂]
    have hev : (fun ξ' => (1 - φ ξ') * (polySymbol n P ξ')⁻¹) =ᶠ[nhds ξ]
        (fun ξ' => (polySymbol n P ξ')⁻¹) := by
      have h_open : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
      have h_mem : ξ ∈ (tsupport φ)ᶜ := hξ_not_supp
      exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨(tsupport φ)ᶜ,
        h_open.mem_nhds h_mem, fun y hy => by
          have hφ0 : φ y = 0 := by
            have : y ∉ Function.support φ := fun hs => hy (subset_tsupport φ hs)
            simpa [Function.mem_support, not_not] using this
          simp [hφ0]⟩
    exact (hev.iteratedFDeriv ℝ k).self_of_nhds

  refine ⟨0, max C_in C_out + 1, fun ξ => ?_⟩
  simp only [pow_zero, mul_one]
  by_cases hξ : ξ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R
  ·
    calc ‖iteratedFDeriv ℝ k (fun ξ' => (1 - φ ξ') * (polySymbol n P ξ')⁻¹) ξ‖
        ≤ C_in := hC_in ξ hξ
      _ ≤ max C_in C_out := le_max_left _ _
      _ ≤ max C_in C_out + 1 := le_add_of_nonneg_right zero_le_one
  ·
    rw [hQ_eq_outside ξ hξ]
    have hξ_norm : R₁ < ‖ξ‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right] at hξ
      linarith [le_max_left R₁ R₂]
    calc ‖iteratedFDeriv ℝ k (fun ξ' => (polySymbol n P ξ')⁻¹) ξ‖
        ≤ C_out := hC_out ξ hξ_norm
      _ ≤ max C_in C_out := le_max_right _ _
      _ ≤ max C_in C_out + 1 := le_add_of_nonneg_right zero_le_one

/-- **Temperate growth of the parametrix symbol.** Combining smoothness
and the polynomial bound on derivatives, the regularised symbol
`(1 - φ(ξ)) · P̂(ξ)⁻¹` has temperate growth — the property needed to apply
it as a Fourier multiplier to tempered distributions. -/
theorem elliptic_parametrix_symbol_hasTemperateGrowth_aux
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_eq_one : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ ≠ 0 ∨ φ ξ = 1)
    (hφ_nhd_zero : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ = 0 → ∀ᶠ η in nhds ξ, φ η = 1) :
    Function.HasTemperateGrowth (fun ξ =>
      (1 - φ ξ) * (polySymbol n P ξ)⁻¹) := by
  constructor
  ·
    rw [contDiff_iff_contDiffAt]
    intro ξ₀
    rcases hφ_eq_one ξ₀ with hP_ne | hφ_one
    ·
      have hP_cd : ContDiff ℝ (⊤ : ℕ∞) (polySymbol n P) :=
        polySymbol_contDiff n P
      exact (contDiffAt_const.sub hφ_smooth.contDiffAt).mul
        (hP_cd.contDiffAt.inv hP_ne)
    · by_cases h : polySymbol n P ξ₀ ≠ 0
      · have hP_cd : ContDiff ℝ (⊤ : ℕ∞) (polySymbol n P) :=
          polySymbol_contDiff n P
        exact (contDiffAt_const.sub hφ_smooth.contDiffAt).mul
          (hP_cd.contDiffAt.inv h)
      ·
        push_neg at h
        exact contDiffAt_parametrix_symbol_at_zero P hP hn φ hφ_smooth hφ_supp hφ_eq_one
          hφ_nhd_zero ξ₀ h hφ_one

  ·
    intro k
    exact parametrix_symbol_iteratedFDeriv_bound P hP hn φ hφ_smooth hφ_supp hφ_eq_one
      hφ_nhd_zero k

/-- **Parametrix symbol/cutoff data package for an elliptic operator.**
Combines the existence of the cutoff `φ`, the regularised symbol
`Q = (1 - φ) · P̂⁻¹`, its temperate growth, and the fact that the
distribution `Q(D) δ₀` is smooth at every nonzero point. -/
theorem elliptic_parametrix_cutoff_data
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P) :
    ∃ (Q φ : EuclideanSpace ℝ (Fin n) → ℂ),
      Function.HasTemperateGrowth Q ∧
      Function.HasTemperateGrowth φ ∧
      HasCompactSupport φ ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ ξ, Q ξ * polySymbol n P ξ = 1 - φ ξ) ∧
      (∀ x₀ : EuclideanSpace ℝ (Fin n), x₀ ≠ 0 →
        isSmoothNear
          (TemperedDistribution.fourierMultiplierCLM ℂ Q
            (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀) := by
  by_cases hn : (0 : ℕ) < n
  ·
    obtain ⟨φ, hφ_smooth, hφ_supp, hφ_eq_one, hφ_nhd_zero⟩ :=
      elliptic_parametrix_cutoff_exists_aux P hP hn

    set Q : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ =>
      (1 - φ ξ) * (polySymbol n P ξ)⁻¹ with hQ_def

    have hQ_temp : Function.HasTemperateGrowth Q :=
      elliptic_parametrix_symbol_hasTemperateGrowth_aux P hP hn φ hφ_smooth hφ_supp hφ_eq_one
        hφ_nhd_zero


    have hφ_temp : Function.HasTemperateGrowth φ :=
      hφ_supp.hasTemperateGrowth hφ_smooth

    have hQP : ∀ ξ, Q ξ * polySymbol n P ξ = 1 - φ ξ := by
      intro ξ
      simp only [hQ_def]
      rcases hφ_eq_one ξ with hP_ne | hφ_one
      ·
        field_simp
      ·
        simp [hφ_one]

    have hQ_smooth := elliptic_parametrix_smooth_away_from_origin hP hn Q hQ_temp
    exact ⟨Q, φ, hQ_temp, hφ_temp, hφ_supp, hφ_smooth, hQP, hQ_smooth⟩
  ·

    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0

    have hφ_supp : HasCompactSupport (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℂ)) := by
      rw [HasCompactSupport]
      have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
      have hmem : tsupport (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℂ)) ⊆ {default} :=
        closure_minimal (fun x _ => hsub.elim x default)
          (Set.Finite.isClosed (Set.finite_singleton _))
      exact IsCompact.of_isClosed_subset isCompact_singleton isClosed_closure hmem
    refine ⟨0, fun _ => 1, Function.HasTemperateGrowth.const 0,
      Function.HasTemperateGrowth.const 1, hφ_supp,
      contDiff_const, fun ξ => ?_, fun x₀ hx₀ => ?_⟩
    · simp
    · exfalso
      exact hx₀ (Subsingleton.elim x₀ 0)

/-- **Temperate growth of the Fourier symbol.** The polynomial symbol
`ξ ↦ P(2πiξ)` has temperate growth. -/
theorem polySymbol_hasTemperateGrowth
    (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    Function.HasTemperateGrowth (polySymbol n P) := by
  suffices h : ∀ Q : MvPolynomial (Fin n) ℂ,
    Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) Q) from h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const c
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    have hcoord : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
        2 * ↑Real.pi * Complex.I * (ξ j : ℂ)) := by
      have hc : Function.HasTemperateGrowth (fun _ : EuclideanSpace ℝ (Fin n) =>
        (2 * ↑Real.pi * Complex.I : ℂ)) := Function.HasTemperateGrowth.const _
      have hx : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) := by
        have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) =
          (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ (EuclideanSpace.proj j) := by
          ext ξ; simp [EuclideanSpace.proj, Complex.ofRealCLM]
        rw [heq]
        exact Complex.ofRealCLM.hasTemperateGrowth.comp (EuclideanSpace.proj j).hasTemperateGrowth
      exact hc.mul hx
    exact hP.mul hcoord

set_option maxHeartbeats 400000 in
/-- **Compactly-supported multipliers give globally smooth distributions.**
If the Fourier multiplier `φ` is smooth and compactly supported, then
`φ(D) δ₀ = ℱ^{-1} φ` is a Schwartz function, hence smooth near every
point. -/
theorem compactSupport_fourierMultiplier_delta_isSmoothNear
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_temp : Function.HasTemperateGrowth φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear
      (TemperedDistribution.fourierMultiplierCLM ℂ φ
        (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀ := by
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
  let φ_sch : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := hφ_compact.toSchwartzMap hφ_smooth
  let f_sch : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := FourierTransformInv.fourierInv φ_sch
  refine ⟨f_sch, f_sch.smooth', fun ψ _ => ?_⟩
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply, TemperedDistribution.delta_apply]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  have heq : ∀ v, (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv ψ)) v =
      φ v • (FourierTransformInv.fourierInv ψ) v :=
    fun v => SchwartzMap.smulLeftCLM_apply_apply hφ_temp _ v
  simp_rw [heq]
  simp_rw [show ∀ y, ψ y • (f_sch : EuclideanSpace ℝ (Fin n) → ℂ) y =
      (f_sch : EuclideanSpace ℝ (Fin n) → ℂ) y • ψ y from fun y => mul_comm _ _]
  exact (SchwartzMap.integral_fourierInv_smul_eq φ_sch ψ).symm

/-- **Full parametrix symbol data for an elliptic operator.** A polished
version of `elliptic_parametrix_cutoff_data` that also records the
temperate growth of the original Fourier symbol and the smoothness of both
distributions `φ(D) δ₀` and `Q(D) δ₀`. -/
theorem elliptic_parametrix_symbol_data_proof
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P) :
    ∃ (Q φ : EuclideanSpace ℝ (Fin n) → ℂ),
      Function.HasTemperateGrowth Q ∧
      Function.HasTemperateGrowth φ ∧
      Function.HasTemperateGrowth (polySymbol n P) ∧
      (∀ ξ, Q ξ * polySymbol n P ξ = 1 - φ ξ) ∧
      (∀ x₀, isSmoothNear
        (TemperedDistribution.fourierMultiplierCLM ℂ φ
          (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀) ∧
      (∀ x₀ : EuclideanSpace ℝ (Fin n), x₀ ≠ 0 →
        isSmoothNear
          (TemperedDistribution.fourierMultiplierCLM ℂ Q
            (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀) := by

  obtain ⟨Q, φ, hQ_temp, hφ_temp, hφ_compact, hφ_smooth, hQP, hQ_smooth⟩ :=
    elliptic_parametrix_cutoff_data hP

  exact ⟨Q, φ,
    hQ_temp,
    hφ_temp,
    polySymbol_hasTemperateGrowth n P,
    hQP,
    fun x₀ => compactSupport_fourierMultiplier_delta_isSmoothNear φ hφ_temp hφ_compact
      hφ_smooth x₀,
    hQ_smooth⟩


/-- **`Q(D) δ₀` is a parametrix.** Given symbol data `(Q, φ)` with
`Q · P̂ = 1 - φ` and `φ(D) δ₀` smooth everywhere, the difference
`P(D) (Q(D) δ₀) - δ₀` equals `-φ(D) δ₀` and is therefore smooth near every
point. In particular `Q(D) δ₀` is a parametrix for `P(D)`. -/
theorem elliptic_parametrix_isParametrix_proof
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P)
    {Q φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hQ : Function.HasTemperateGrowth Q)
    (hφ : Function.HasTemperateGrowth φ)
    (hPt : Function.HasTemperateGrowth (polySymbol n P))
    (hQP : ∀ ξ, Q ξ * polySymbol n P ξ = 1 - φ ξ)
    (hφs : ∀ x₀, isSmoothNear
      (TemperedDistribution.fourierMultiplierCLM ℂ φ
        (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear
      (constCoeffDiffOp n P
        (TemperedDistribution.fourierMultiplierCLM ℂ Q
          (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) -
       TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))) x₀ := by

  set δ₀ := TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))


  have hcomp : constCoeffDiffOp n P
      (TemperedDistribution.fourierMultiplierCLM ℂ Q δ₀) =
      TemperedDistribution.fourierMultiplierCLM ℂ (Q * polySymbol n P) δ₀ := by
    simp only [constCoeffDiffOp]
    exact TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hQ hPt δ₀
  have hQP_eq : Q * polySymbol n P = 1 - φ := by
    ext ξ; exact hQP ξ
  have hkey : constCoeffDiffOp n P
      (TemperedDistribution.fourierMultiplierCLM ℂ Q δ₀) - δ₀ =
      -(TemperedDistribution.fourierMultiplierCLM ℂ φ δ₀) := by
    rw [hcomp, hQP_eq]

    have h1φ : Function.HasTemperateGrowth (1 - φ) :=
      (Function.HasTemperateGrowth.const (1 : ℂ)).sub hφ
    ext u
    simp only [TemperedDistribution.fourierMultiplierCLM_apply_apply,
      UniformConvergenceCLM.sub_apply, UniformConvergenceCLM.neg_apply]
    have hsum : SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u) +
        SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u) =
        FourierTransformInv.fourierInv u := by
      ext x
      simp only [SchwartzMap.add_apply]
      rw [SchwartzMap.smulLeftCLM_apply_apply h1φ, SchwartzMap.smulLeftCLM_apply_apply hφ]
      simp [Pi.sub_apply, smul_eq_mul, sub_mul, one_mul, sub_add_cancel]
    have hab : FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u)) +
        FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u)) = u := by
      rw [← FourierAdd.fourier_add, hsum, FourierTransform.fourier_fourierInv_eq]
    have hlin : δ₀ (FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u))) +
        δ₀ (FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u))) = δ₀ u := by
      rw [← map_add δ₀, hab]
    linear_combination hlin

  rw [hkey]

  obtain ⟨U, hU_open, hx₀_U, f, hf_smooth, hf_eq⟩ := hφs x₀
  exact ⟨U, hU_open, hx₀_U, -f, hf_smooth.neg, fun ψ hψ => by
    simp only [UniformConvergenceCLM.neg_apply, hf_eq ψ hψ, Pi.neg_apply, smul_neg,
      integral_neg]⟩


/-- **Pointwise singular-support bound for an elliptic parametrix.** Any
parametrix `F` for an elliptic operator `P(D)` is smooth at every nonzero
point. Proven by comparing `F` to the explicit Fourier-multiplier
parametrix `F₀ = Q(D) δ₀` via `parametrix_inversion_isSmoothNear`. -/
theorem elliptic_parametrix_singSupp_at_point
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hF : IsParametrix P F)
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ : Function.HasTemperateGrowth Q)
    (hQs : ∀ x₀ : EuclideanSpace ℝ (Fin n), x₀ ≠ 0 →
      isSmoothNear (TemperedDistribution.fourierMultiplierCLM ℂ Q
        (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ≠ 0) :
    isSmoothNear F x := by

  obtain ⟨Q', φ, hQ'_temp, hφ_temp, hP_temp, hQ'P, hφ_smooth, hQ'_smooth⟩ :=
    elliptic_parametrix_symbol_data_proof hP
  set δ₀ := TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  set F₀ := TemperedDistribution.fourierMultiplierCLM ℂ Q' δ₀

  have hF₀_param : IsParametrix P F₀ := by
    rw [IsParametrix, Set.eq_empty_iff_forall_notMem]
    intro x₀ hx₀
    exact hx₀ (elliptic_parametrix_isParametrix_proof hP hQ'_temp hφ_temp hP_temp hQ'P
      hφ_smooth x₀)

  have hF₀_sing : singularSupport F₀ ⊆ {(0 : EuclideanSpace ℝ (Fin n))} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    by_contra hyne
    exact hy (hQ'_smooth y hyne)


  have hPF_sub_delta_smooth : isSmoothNear (constCoeffDiffOp n P F - δ₀) x := by
    have h := hF
    rw [IsParametrix, singularSupport] at h
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not] at h
    exact h x

  have hδ_smooth : isSmoothNear δ₀ x := by
    refine ⟨{(0 : EuclideanSpace ℝ (Fin n))}ᶜ, isOpen_compl_singleton, ?_, 0, contDiff_const,
      fun ψ hψ => ?_⟩
    · exact Set.mem_compl_singleton_iff.mpr hx
    · simp only [Pi.zero_apply, smul_zero, MeasureTheory.integral_zero]
      have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉
          ({(0 : EuclideanSpace ℝ (Fin n))} : Set (EuclideanSpace ℝ (Fin n)))ᶜ := by
        simp
      exact hψ 0 h0

  have hPF_smooth : isSmoothNear (constCoeffDiffOp n P F) x := by
    obtain ⟨U₁, hU₁_open, hx_U₁, f₁, hf₁_smooth, hf₁_eq⟩ := hPF_sub_delta_smooth
    obtain ⟨U₂, hU₂_open, hx_U₂, f₂, hf₂_smooth, hf₂_eq⟩ := hδ_smooth
    refine ⟨U₁ ∩ U₂, hU₁_open.inter hU₂_open, ⟨hx_U₁, hx_U₂⟩, f₁ + f₂,
      hf₁_smooth.add hf₂_smooth, fun ψ hψ => ?_⟩
    have hψ_U₁ : ∀ y, y ∉ U₁ → ψ y = 0 := fun y hy =>
      hψ y (fun ⟨h1, _⟩ => hy h1)
    have hψ_U₂ : ∀ y, y ∉ U₂ → ψ y = 0 := fun y hy =>
      hψ y (fun ⟨_, h2⟩ => hy h2)

    have hsplit : (constCoeffDiffOp n P F) ψ =
        (constCoeffDiffOp n P F - δ₀) ψ + δ₀ ψ := by
      simp only [UniformConvergenceCLM.sub_apply]
      ring
    rw [hsplit, hf₁_eq ψ hψ_U₁, hf₂_eq ψ hψ_U₂]
    rw [← MeasureTheory.integral_add
      (schwartz_smul_smooth_integrable (constCoeffDiffOp n P F - δ₀) U₁ hU₁_open f₁
        hf₁_smooth hf₁_eq ψ hψ_U₁)
      (schwartz_smul_smooth_integrable δ₀ U₂ hU₂_open f₂ hf₂_smooth hf₂_eq ψ hψ_U₂)]
    congr 1; ext z; exact (smul_add (ψ z) (f₁ z) (f₂ z)).symm

  exact parametrix_inversion_isSmoothNear P F₀ hF₀_param hF₀_sing F x hPF_smooth

/-- **Existence of a parametrix for an elliptic operator.** Every elliptic
constant-coefficient `P(D)` admits a parametrix, constructed as
`F = Q(D) δ₀` with the regularised symbol `Q`. -/
theorem elliptic_parametrix_exists
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P) :
    ∃ (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      IsParametrix P F := by
  obtain ⟨Q, φ, hQ_temp, hφ_temp, hP_temp, hQP, hφ_smooth, _⟩ :=
    elliptic_parametrix_symbol_data_proof hP
  let δ₀ := TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  refine ⟨TemperedDistribution.fourierMultiplierCLM ℂ Q δ₀, ?_⟩
  rw [IsParametrix, Set.eq_empty_iff_forall_notMem]
  intro x₀ hx₀
  exact hx₀ (elliptic_parametrix_isParametrix_proof hP hQ_temp hφ_temp hP_temp hQP
    hφ_smooth x₀)

/-- **Singular-support bound for an elliptic parametrix.** Every parametrix
`F` for an elliptic `P(D)` has singular support contained in `{0}`. -/
theorem elliptic_parametrix_singSupp_bound
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hF : IsParametrix P F) :
    singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))} := by
  obtain ⟨Q, _, hQ_temp, _, _, _, _, hQ_smooth⟩ :=
    elliptic_parametrix_symbol_data_proof hP
  intro x hx
  rw [Set.mem_singleton_iff]
  by_contra hne
  exact hx (elliptic_parametrix_singSupp_at_point hP F hF Q hQ_temp hQ_smooth x hne)

/-- **Existence of a parametrix with controlled singular support.**
Combining existence and the singular-support bound: every elliptic `P(D)`
has a parametrix `F` whose singular support is contained in `{0}`. This is
exactly the hypothesis required by `IsHypoelliptic`. -/
theorem parametrix_exists_with_singSupp
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P) :
    ∃ (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      IsParametrix P F ∧
      singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))} := by
  obtain ⟨F, hFparam⟩ := elliptic_parametrix_exists hP
  exact ⟨F, hFparam, elliptic_parametrix_singSupp_bound hP F hFparam⟩

/-- **Theorem 11.12 (Melrose).** Every elliptic constant-coefficient
operator `P(D)` is hypoelliptic: it admits a parametrix with singular
support `⊆ {0}`. -/
theorem IsElliptic.isHypoelliptic {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P) :
    IsHypoelliptic P := by
  obtain ⟨F, hParam, hSing⟩ := parametrix_exists_with_singSupp hP
  exact ⟨F, hParam, hSing⟩

end EllipticHypoelliptic

section PoissonEquation

open Filter Topology

variable {n}

/-- A **smooth function vanishing at infinity** (with all derivatives):
a smooth complex-valued function on `ℝⁿ` whose iterated derivatives of
every order tend to zero on the cocompact filter. Used as the target class
for Liouville-type uniqueness results for the Laplacian. -/
structure SmoothZeroAtInfty (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  smooth' : ContDiff ℝ (⊤ : ℕ∞) toFun
  iteratedFDeriv_zero_at_infty' (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m toFun x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

namespace SmoothZeroAtInfty

variable {n : ℕ}

/-- `SmoothZeroAtInfty` is coercible to a function via its underlying
`toFun` field, with the obvious injectivity. -/
instance instFunLike : FunLike (SmoothZeroAtInfty n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe u := u.toFun
  coe_injective' u v h := by cases u; cases v; congr

/-- Pointwise equality of `SmoothZeroAtInfty` functions implies equality. -/
@[ext]
theorem ext {u v : SmoothZeroAtInfty n} (h : ∀ x, u x = v x) : u = v :=
  DFunLike.ext u v h

/-- Smoothness of the underlying function of a `SmoothZeroAtInfty`. -/
theorem smooth (u : SmoothZeroAtInfty n) : ContDiff ℝ (⊤ : ℕ∞) u :=
  u.smooth'

/-- For every order `m`, the norm of the `m`-th iterated derivative of a
`SmoothZeroAtInfty` function tends to zero on the cocompact filter. -/
theorem iteratedFDeriv_zero_at_infty (u : SmoothZeroAtInfty n) (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m u x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
  u.iteratedFDeriv_zero_at_infty' m

end SmoothZeroAtInfty

/-- The **Laplacian polynomial** `P(X) = Σⱼ Xⱼ²`, whose associated
constant-coefficient differential operator is the Laplacian
`Δ = Σⱼ ∂ⱼ²` (up to the usual `(2πi)²` factor coming from the Fourier
normalisation). -/
def laplacianPoly : MvPolynomial (Fin n) ℂ :=
  ∑ j : Fin n, MvPolynomial.X j ^ 2

/-- The **Laplacian** as a continuous linear operator on tempered
distributions, defined via the constant-coefficient differential operator
machinery applied to `laplacianPoly`. -/
def laplacianOp :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  constCoeffDiffOp n (laplacianPoly)

end PoissonEquation

end DifferentialOperators

namespace DifferentialOperators

/-- **Smoothness of polynomial evaluation.** Evaluating a real multivariate
polynomial on the coordinates of `ℝⁿ` yields a `C^∞` function. -/
lemma contDiff_mvPolynomial_eval {n₀ : ℕ} (Q : MvPolynomial (Fin n₀) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n₀) =>
      MvPolynomial.eval (fun i => ξ i) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C]; exact contDiff_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_piLp_apply 2)

/-- **Closed-form norm of derivatives of `1/x`.** On an open subset of
`ℝ`, the norm of the `k`-th iterated Fréchet derivative of `x ↦ x⁻¹`
equals `k! · ‖y‖^{-(k+1)}`. -/
lemma norm_iteratedFDerivWithin_inv_eq (k : ℕ) (y : ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hys : y ∈ s) :
    ‖iteratedFDerivWithin ℝ k Inv.inv s y‖ = ↑(k.factorial) * ‖y‖⁻¹ ^ (k + 1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have hfun : Inv.inv = fun z : ℝ => 1 / z := by ext z; exact (one_div z).symm
  rw [hfun, iteratedDerivWithin_one_div k hs hys]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  rw [show (-1 : ℤ) - ↑k = -(↑(k + 1) : ℤ) by omega]
  rw [zpow_neg, norm_inv, zpow_natCast, norm_pow, one_div, inv_pow]


/-- **Smoothness of `1/P(ξ)` at non-vanishing points.** Wherever the
polynomial `P` does not vanish, the function `ξ ↦ 1/P(ξ)` is `C^∞`. -/
lemma contDiffAt_inv_mvPolynomial_eval {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n₀))
    (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ :=
  (contDiff_mvPolynomial_eval P).contDiffAt.inv hP

/-- **Explicit derivative of `1/P(ξ)`.** At any non-vanishing point, the
Fréchet derivative of `ξ ↦ 1/P(ξ)` equals `-P(ξ)⁻² · dP(ξ)`. -/
lemma hasFDerivAt_inv_mvPolynomial_eval {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n₀))
    (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
    HasFDerivAt (fun ξ' : EuclideanSpace ℝ (Fin n₀) => (MvPolynomial.eval (fun i => ξ' i) P)⁻¹)
      (-(MvPolynomial.eval (fun i => ξ i) P)⁻¹ ^ 2 •
        fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
          MvPolynomial.eval (fun i => ξ' i) P) ξ)
      ξ := by
  have hP_diff : HasFDerivAt
      (fun ξ' : EuclideanSpace ℝ (Fin n₀) => MvPolynomial.eval (fun i => ξ' i) P)
      (fderiv ℝ (fun ξ' => MvPolynomial.eval (fun i => ξ' i) P) ξ) ξ :=
    ((contDiff_mvPolynomial_eval P).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hasFDerivAt_inv hP).comp ξ hP_diff
  convert h using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm, sq, inv_mul_eq_div]

/-- **Norm bound for the derivative of `1/P(ξ)`.** Combining the explicit
formula with the multiplicativity of norms,
`‖d(1/P)(ξ)‖ ≤ ‖dP(ξ)‖ / ‖P(ξ)‖²`. -/
lemma norm_fderiv_inv_mvPolynomial_eval_le {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n₀))
    (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
    ‖fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ‖ ≤
      ‖fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
        MvPolynomial.eval (fun i => ξ' i) P) ξ‖ /
        ‖MvPolynomial.eval (fun i => ξ i) P‖ ^ 2 := by
  rw [(hasFDerivAt_inv_mvPolynomial_eval P ξ hP).fderiv]
  rw [norm_smul, norm_neg, norm_pow, norm_inv, inv_pow, div_eq_mul_inv, mul_comm]

/-- **Recursive identity for higher derivatives of `1/P`.** The norm of the
`(k+1)`-th iterated derivative of `1/P` equals the norm of the `k`-th
iterated derivative of its first derivative. -/
lemma norm_iteratedFDeriv_succ_eq_norm_iteratedFDeriv_fderiv_inv_poly
    {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ) (k : ℕ)
    (ξ : EuclideanSpace ℝ (Fin n₀)) :
    ‖iteratedFDeriv ℝ (k + 1) (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ‖ =
    ‖iteratedFDeriv ℝ k (fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹)) ξ‖ :=
  norm_iteratedFDeriv_fderiv.symm

end DifferentialOperators


namespace DifferentialOperators

open MeasureTheory

/-- **Non-degeneracy of the Laplacian polynomial.** For `n ≥ 1`,
`Σⱼ Xⱼ²` is nonzero in `ℂ[X₀, …, X_{n-1}]`. -/
lemma laplacianPoly_ne_zero {n : ℕ} (hn : 1 ≤ n) : laplacianPoly (n := n) ≠ 0 := by
  unfold laplacianPoly
  intro h
  have h0 : Fin n := ⟨0, by omega⟩
  let e₀ : Fin n → ℂ := fun j => if j = h0 then 1 else 0
  have heval := congr_arg (MvPolynomial.eval e₀) h
  simp only [map_sum, map_zero, MvPolynomial.eval_pow, MvPolynomial.eval_X] at heval
  have key : (e₀ h0) ^ 2 = 1 := by simp [e₀]
  have hterm : ∑ j : Fin n, (e₀ j) ^ 2 = 1 := by
    have hzero : ∀ j : Fin n, j ≠ h0 → (e₀ j) ^ 2 = 0 := by
      intro j hj; simp [e₀, hj]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ h0)]
    rw [key]
    have : ∑ j ∈ Finset.univ.erase h0, (e₀ j) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hzero j (Finset.ne_of_mem_erase hj)
    rw [this]; ring
  exact one_ne_zero (hterm.symm.trans heval)


open Filter Topology

/-- The **classical Laplacian relation** between smooth functions
`f, g : ℝⁿ → ℂ`: `g(x) = -Σⱼ ∂_j² f(x)` for every `x`. (The convention sign
comes from the Fourier multiplier `-|2πξ|²` of `Δ`.) -/
def IsLaplacianOf_DO (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    g x = -∑ j : Fin n,
      (iteratedFDeriv ℝ 2 f x) (fun _ => EuclideanSpace.single j (1 : ℝ))


/-- **Integration-by-parts formula for the Laplacian on a smooth
representative.** If a tempered distribution `u_td` is represented by a
smooth function `u` vanishing at infinity (with all derivatives), then for
every Schwartz test function `φ`, applying the distributional Laplacian
equals the integral of `φ` against the classical Laplacian `-Σⱼ ∂_j² u`. -/
theorem laplacianOp_smooth_eq_classical_DO
    {n : ℕ} (hn : 3 ≤ n)
    (u : SmoothZeroAtInfty n)
    (u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu_td : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td φ = ∫ x, φ x • u x) :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (laplacianOp u_td) φ =
        ∫ x, φ x • (-∑ j : Fin n,
          (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ))) := by sorry


/-- **A continuous function is determined by its pairing with Schwartz
functions.** If the classical Laplacian `-Σⱼ ∂_j² u` and a Schwartz
function `f` agree as integrands against every Schwartz `φ`, then they
agree pointwise. -/
theorem schwartz_determines_continuous_DO
    {n : ℕ} (hn : 3 ≤ n)
    (u : SmoothZeroAtInfty n)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (∫ x, φ x • (-∑ j : Fin n,
        (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ)))) =
      ∫ x, φ x • f x) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (f : EuclideanSpace ℝ (Fin n) → ℂ) x =
        -∑ j : Fin n,
          (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ)) := by sorry

/-- **Distributional Laplacian equals classical Laplacian (pointwise).**
For smooth `u` vanishing at infinity (along with all derivatives) and
Schwartz `f`, if the distributional Laplacian of `u` equals `f`, then
`f = -Σⱼ ∂_j² u` pointwise. -/
theorem distributional_laplacian_eq_pointwise_DO
    {n : ℕ} (hn : 3 ≤ n)
    (u : SmoothZeroAtInfty n)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu_td : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td φ = ∫ x, φ x • u x)
    (hlap : laplacianOp u_td = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))) :
    IsLaplacianOf_DO n (⇑u) (⇑f) := by
  have h_ibp := laplacianOp_smooth_eq_classical_DO hn u u_td hu_td
  intro x
  have h_dist_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (∫ x, φ x • (-∑ j : Fin n,
        (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ)))) =
      ∫ x, φ x • f x := by
    intro φ
    have h1 := h_ibp φ
    have h2 : (laplacianOp u_td) φ =
        (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) φ := congr_fun (congr_arg _ hlap) φ
    rw [← h1, h2, SchwartzMap.coe_apply]
  exact schwartz_determines_continuous_DO hn u f h_dist_eq x


/-- **Mean-value gradient bound for a harmonic function.** For a smooth
harmonic function `u : ℝⁿ → ℂ` bounded in absolute value by `C`, the
Fréchet derivative at any point `a` satisfies the gradient estimate
`‖du(a)‖ ≤ n · C / R` for every `R > 0`. -/
theorem harmonic_fderiv_norm_le_div_DO
    {n : ℕ} (hn : 1 ≤ n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : IsLaplacianOf_DO n u 0)
    (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, ‖u x‖ ≤ C)
    (R : ℝ) (hR : 0 < R) (a : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ u a‖ ≤ ↑n * C / R := by sorry

/-- **Bounded harmonic functions have vanishing gradient.** Letting `R → ∞`
in the gradient estimate forces `du(x) = 0` at every point. -/
theorem bounded_harmonic_fderiv_eq_zero_DO
    {n : ℕ} (hn : 1 ≤ n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : IsLaplacianOf_DO n u 0)
    (hbd : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) :
    ∀ x, fderiv ℝ u x = 0 := by
  obtain ⟨C₀, hC₀⟩ := hbd
  set C := max C₀ 0
  have hC_nn : 0 ≤ C := le_max_right _ _
  have hbd' : ∀ x, ‖u x‖ ≤ C := fun x => (hC₀ x).trans (le_max_left _ _)
  intro x
  rw [← norm_le_zero_iff]
  by_contra h_pos
  push Not at h_pos
  set M := ↑n * C
  have hM : 0 ≤ M := by positivity
  rcases eq_or_lt_of_le hM with hM0 | hM_pos
  · have hge := harmonic_fderiv_norm_le_div_DO hn u hsmooth hharm C hC_nn hbd' 1 one_pos x
    simp only [show ↑n * C = (0 : ℝ) from hM0.symm, zero_div] at hge; linarith
  · have hge := harmonic_fderiv_norm_le_div_DO hn u hsmooth hharm C hC_nn hbd'
      (2 * M / ‖fderiv ℝ u x‖) (by positivity) x
    have : M / (2 * M / ‖fderiv ℝ u x‖) = ‖fderiv ℝ u x‖ / 2 := by field_simp
    rw [this] at hge; linarith

/-- **Liouville's theorem (smooth version).** A bounded smooth harmonic
function on `ℝⁿ` is constant. -/
theorem bounded_harmonic_is_constant_DO
    {n : ℕ} (hn : 1 ≤ n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : IsLaplacianOf_DO n u 0)
    (hbd : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) :
    ∃ c : ℂ, u = Function.const _ c := by
  have hfderiv := bounded_harmonic_fderiv_eq_zero_DO hn u hsmooth hharm hbd
  exact ⟨u 0, funext fun x =>
    is_const_of_fderiv_eq_zero (hsmooth.differentiable (by simp)) hfderiv x 0⟩

/-- **Uniqueness for the Poisson equation.** Among smooth functions on
`ℝⁿ` (`n ≥ 3`) that vanish at infinity, the Laplacian determines the
function uniquely: if `Δu₁ = Δu₂ = f` then `u₁ = u₂`. -/
theorem laplacian_injective_DO
    {n : ℕ} (hn : 3 ≤ n)
    (u₁ u₂ : SmoothZeroAtInfty n)
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (h₁ : IsLaplacianOf_DO n (⇑u₁) f) (h₂ : IsLaplacianOf_DO n (⇑u₂) f) :
    u₁ = u₂ := by
  have hn1 : 1 ≤ n := le_trans (by norm_num : 1 ≤ 3) hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  haveI : NoncompactSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  set v : EuclideanSpace ℝ (Fin n) → ℂ := fun x => u₁ x - u₂ x
  have hv_smooth : ContDiff ℝ (⊤ : ℕ∞) v := u₁.smooth'.sub u₂.smooth'
  have hv_eq : v = ⇑u₁ - ⇑u₂ := rfl

  have hv_norm_tend : Tendsto (fun x => ‖v x‖) (cocompact _) (𝓝 0) := by
    have h1 := u₁.iteratedFDeriv_zero_at_infty' 0
    have h2 := u₂.iteratedFDeriv_zero_at_infty' 0
    simp at h1 h2
    exact squeeze_zero (fun x => norm_nonneg _) (fun x => norm_sub_le _ _)
      (by simpa using h1.add h2)

  have hv_harm : IsLaplacianOf_DO n v 0 := by
    intro x; simp only [Pi.zero_apply]
    have hsub2 : iteratedFDeriv ℝ 2 v x =
        iteratedFDeriv ℝ 2 (⇑u₁) x - iteratedFDeriv ℝ 2 (⇑u₂) x := by
      rw [hv_eq]
      exact congr_fun (iteratedFDeriv_sub (u₁.smooth'.of_le (WithTop.coe_le_coe.mpr le_top))
        (u₂.smooth'.of_le (WithTop.coe_le_coe.mpr le_top)) (i := 2)) x
    simp only [hsub2, ContinuousMultilinearMap.sub_apply, Finset.sum_sub_distrib]
    rw [eq_comm, neg_eq_zero, sub_eq_zero]
    exact neg_inj.mp ((h₁ x).symm.trans (h₂ x))

  have hv_bounded : ∃ C : ℝ, ∀ x, ‖v x‖ ≤ C := by
    have hev : ∀ᶠ x in cocompact _, ‖v x‖ < 1 := hv_norm_tend (Iio_mem_nhds one_pos)
    rw [Filter.hasBasis_cocompact.eventually_iff] at hev
    simp only [Set.mem_compl_iff] at hev
    obtain ⟨K, hK, hKv⟩ := hev
    by_cases hKne : K.Nonempty
    · obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hv_smooth.continuous.continuousOn
      exact ⟨max M 1, fun x => by
        by_cases hxK : x ∈ K
        · exact (hM x hxK).trans (le_max_left M 1)
        · exact (le_of_lt (hKv hxK)).trans (le_max_right M 1)⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      exact ⟨1, fun x => le_of_lt (hKv (by simp [hKne]))⟩

  obtain ⟨c, hc⟩ := bounded_harmonic_is_constant_DO hn1 v hv_smooth hv_harm hv_bounded

  have hc_zero : c = 0 := by
    have : ∀ x, v x = c := fun x => congr_fun hc x
    simp_rw [this] at hv_norm_tend
    exact norm_eq_zero.mp (tendsto_nhds_unique hv_norm_tend tendsto_const_nhds).symm

  ext x
  have hx := congr_fun hc x
  change u₁ x - u₂ x = c at hx
  rw [hc_zero] at hx
  exact sub_eq_zero.mp hx

/-- **Uniqueness for `Δ u = f`** with Schwartz right-hand side, among
distributional solutions represented by smooth functions vanishing at
infinity (i.e. in `C₀^∞`). -/
theorem laplacian_schwartz_uniqueness_C0infty
    {n : ℕ} (hn : 3 ≤ n) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∀ (u₁ u₂ : SmoothZeroAtInfty n)
      (u_td₁ u_td₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td₁ φ = ∫ x, φ x • u₁ x) →
      laplacianOp u_td₁ = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) →
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td₂ φ = ∫ x, φ x • u₂ x) →
      laplacianOp u_td₂ = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) →
      u₁ = u₂ := by
  intro u₁ u₂ u_td₁ u_td₂ hu_td₁ hlap₁ hu_td₂ hlap₂
  have h₁ : IsLaplacianOf_DO n (⇑u₁) (⇑f) :=
    distributional_laplacian_eq_pointwise_DO hn u₁ f u_td₁ hu_td₁ hlap₁
  have h₂ : IsLaplacianOf_DO n (⇑u₂) (⇑f) :=
    distributional_laplacian_eq_pointwise_DO hn u₂ f u_td₂ hu_td₂ hlap₂
  exact laplacian_injective_DO hn u₁ u₂ (⇑f) h₁ h₂


end DifferentialOperators

open SchwartzMap MeasureTheory Distribution

open scoped Topology

namespace Distribution

section SingularSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [BorelSpace E]

/-- A tempered distribution `u` is **smooth on** the set `s` if there
is a globally smooth `g : E → ℂ` such that `u φ = ∫ φ g` for every
Schwartz function `φ` with `tsupport φ ⊆ s`. -/
def IsSmoothOn (u : 𝓢'(E, ℂ)) (s : Set E) : Prop :=
  ∃ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
    ∀ φ : 𝓢(E, ℂ), tsupport φ ⊆ s → u φ = ∫ x, φ x • g x

/-- The **singular support** of `u`: complement of the union of all open
sets on which `u` is represented by a smooth function. -/
def singularSupport (u : 𝓢'(E, ℂ)) : Set E :=
  (⋃₀ {s | IsSmoothOn u s ∧ IsOpen s})ᶜ

end SingularSupport

end Distribution
end

noncomputable section

open scoped SchwartzMap Topology
open Distribution SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace DifferentialOperators

/-- A tempered distribution `v` has **compact distributional support** if
its `dsupport` is a compact subset of the underlying space. -/
def HasCompactDsupport {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : 𝓢'(E, F)) : Prop :=
  IsCompact (dsupport v)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


/-- **Continuity of translation** on Schwartz space. The map
`x ↦ ψ(· - x)` from `E` to `𝓢(E, ℂ)` is continuous. -/
theorem schwartz_compSubConstCLM_continuous
    (ψ : 𝓢(E, ℂ)) :
    Continuous (fun x : E => compSubConstCLM ℂ x ψ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, (schwartz_withSeminorms ℂ E ℂ).tendsto_nhds]
  intro ⟨k, n⟩ ε hε
  set C := 2 ^ k * (Finset.Iic (k, n + 1)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ
  set Kx := (1 + ‖x₀‖) ^ k * 2 ^ k
  set K := Kx * C
  set δ := min 1 (ε / (K + 1))
  have hδ_pos : 0 < δ := by positivity
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, fun {x} hx => ?_⟩
  rw [dist_eq_norm] at hx
  have hx1 : ‖x - x₀‖ ≤ 1 := le_trans (le_of_lt hx) (min_le_left _ _)
  show (schwartzSeminormFamily ℂ E ℂ (k, n)) _ < ε
  rw [SchwartzMap.compSubConstCLM_sub_eq ψ x x₀]
  set φ := SchwartzMap.compSubConstCLM ℂ (x - x₀) ψ - ψ
  have hbound := TemperedDistributions.SchwartzMap.seminorm_compSubConst_le ℂ k n φ x₀
  have hsup_bound : ((Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)) φ ≤
      C * ‖x - x₀‖ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro ⟨j, m⟩ hjm
    rw [Finset.mem_Iic] at hjm
    have hj : j ≤ k := hjm.1
    have hm : m ≤ n := hjm.2
    have hsub := SchwartzMap.seminorm_translate_sub_le ψ j m (x - x₀) hx1
    have h2pow : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
    have hfin_mono : (Finset.Iic (j, m + 1)).sup (fun p => SchwartzMap.seminorm (𝕜 := ℂ) (E := E) (F := ℂ) p.1 p.2) ≤
        (Finset.Iic (k, n + 1)).sup (fun p => SchwartzMap.seminorm (𝕜 := ℂ) (E := E) (F := ℂ) p.1 p.2) := by
      apply Finset.sup_mono
      intro ⟨a, b⟩ hab
      simp only [Finset.mem_Iic] at hab ⊢
      exact ⟨le_trans hab.1 hj, le_trans hab.2 (Nat.succ_le_succ hm)⟩
    calc (SchwartzMap.seminorm ℂ j m) φ
        ≤ 2 ^ j * (Finset.Iic (j, m + 1)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) ψ *
            ‖x - x₀‖ := hsub
      _ ≤ 2 ^ k * (Finset.Iic (k, n + 1)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) ψ *
            ‖x - x₀‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul h2pow (hfin_mono ψ) (by positivity) (by positivity)
      _ = C * ‖x - x₀‖ := by ring
  calc (schwartzSeminormFamily ℂ E ℂ (k, n)) (SchwartzMap.compSubConstCLM ℂ x₀ φ)
      ≤ Kx * (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ := hbound
    _ ≤ Kx * (C * ‖x - x₀‖) := mul_le_mul_of_nonneg_left hsup_bound (by positivity)
    _ < ε := by
        have hK_nonneg : 0 ≤ K := by positivity
        have hK1 : 0 < K + 1 := by positivity
        calc Kx * (C * ‖x - x₀‖)
            ≤ Kx * (C * δ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left (le_of_lt hx) (by positivity)
          _ = K * δ := by ring
          _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK_nonneg
          _ < ε := by
              have : K / (K + 1) < 1 := by rw [div_lt_one hK1]; linarith
              calc K * (ε / (K + 1)) = (K / (K + 1)) * ε := by ring
                _ < 1 * ε := mul_lt_mul_of_pos_right this hε
                _ = ε := one_mul ε

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `n`-th iterated derivative of `z ↦ fderiv f z h` factors through
the application map `T ↦ T h`. -/
theorem iteratedFDeriv_fderiv_apply_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ}
    (f : E → F) (hf : ContDiff ℝ (↑(n + 1) : WithTop ℕ∞) f) (h : E) (y : E) :
    iteratedFDeriv ℝ n (fun z => (fderiv ℝ f z) h) y =
      (ContinuousLinearMap.apply ℝ F h).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fderiv ℝ f) y) := by
  have hfderiv : ContDiffAt ℝ (↑n : WithTop ℕ∞) (fderiv ℝ f) y := by
    have : ContDiff ℝ (↑n + 1 : WithTop ℕ∞) f := by exact_mod_cast hf
    exact (contDiff_succ_iff_fderiv.mp this).2.2.contDiffAt
  exact (ContinuousLinearMap.apply ℝ F h).iteratedFDeriv_comp_left hfderiv le_rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Norm bound: `‖∂ⁿ (z ↦ Df(z)·h)‖ ≤ ‖∂ⁿ⁺¹ f‖ · ‖h‖`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ}
    (f : E → F) (hf : ContDiff ℝ (↑(n + 1) : WithTop ℕ∞) f) (h : E) (y : E) :
    ‖iteratedFDeriv ℝ n (fun z => (fderiv ℝ f z) h) y‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖h‖ := by
  have hfderiv : ContDiffAt ℝ (↑n : WithTop ℕ∞) (fderiv ℝ f) y := by
    have : ContDiff ℝ (↑n + 1 : WithTop ℕ∞) f := by exact_mod_cast hf
    exact (contDiff_succ_iff_fderiv.mp this).2.2.contDiffAt
  have hle := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ f) (c := h) (x := y)
    hfderiv (le_refl _)
  rw [norm_iteratedFDeriv_fderiv] at hle
  linarith [mul_comm ‖h‖ ‖iteratedFDeriv ℝ (n + 1) f y‖]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Taylor remainder estimate.** For a `C²` map `g`, the first-order
Taylor remainder is `O(‖h‖²)` with constant given by a bound on the second
derivative. -/
theorem norm_iteratedFDeriv_taylor_remainder_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (hg : ContDiff ℝ 2 g) (C : ℝ)
    (hC : ∀ z : E, ‖iteratedFDeriv ℝ 2 g z‖ ≤ C)
    (y h : E) :
    ‖g (y - h) - g y + (fderiv ℝ g y) h‖ ≤ C * ‖h‖ ^ 2 := by

  set Φ : E → F := fun z => g z - g y - (fderiv ℝ g y) (z - y) with hΦ_def
  have hΦy : Φ y = 0 := by simp [hΦ_def, sub_self]
  have hΦyh : Φ (y - h) = g (y - h) - g y + (fderiv ℝ g y) h := by
    simp only [hΦ_def, map_sub]; abel
  have hne2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hg_diff : Differentiable ℝ g := hg.differentiable hne2

  have hΦ_hasFDeriv : ∀ z, HasFDerivAt Φ (fderiv ℝ g z - fderiv ℝ g y) z := by
    intro z
    have hg_has : HasFDerivAt g (fderiv ℝ g z) z := (hg_diff z).hasFDerivAt
    have h1 : HasFDerivAt (fun w => g w - g y) (fderiv ℝ g z) z := by
      have h := hg_has.sub (hasFDerivAt_const (g y) z); rwa [sub_zero] at h
    have h2 : HasFDerivAt (fun w => (fderiv ℝ g y) (w - y)) (fderiv ℝ g y) z := by
      have hsub : HasFDerivAt (fun w => w - y) (ContinuousLinearMap.id ℝ E) z := by
        have h := (hasFDerivAt_id (𝕜 := ℝ) z).sub (hasFDerivAt_const y z); rwa [sub_zero] at h
      have h := (fderiv ℝ g y).hasFDerivAt.comp z hsub; rwa [ContinuousLinearMap.comp_id] at h
    convert h1.sub h2 using 1

  have hfderiv_g_diff : Differentiable ℝ (fderiv ℝ g) := by
    have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := by
      have : ContDiff ℝ (↑(1 : ℕ) + 1 : WithTop ℕ∞) g := by exact_mod_cast hg
      exact (contDiff_succ_iff_fderiv.mp this).2.2
    exact hg1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

  have hfderiv_fderiv_bound : ∀ w : E, ‖fderiv ℝ (fderiv ℝ g) w‖ ≤ C := by
    intro w
    have heq : ‖fderiv ℝ (fderiv ℝ g) w‖ = ‖iteratedFDeriv ℝ 2 g w‖ := by
      conv_rhs => rw [show (2 : ℕ) = 1 + 1 from rfl]
      rw [← norm_iteratedFDeriv_fderiv (n := 1),
        ← norm_iteratedFDeriv_fderiv (n := 0) (f := fderiv ℝ g)]
      simp
    linarith [hC w]

  have hinner_mvt : ∀ z : E, ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖z - y‖ := by
    intro z
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (fun x _ => hfderiv_g_diff x) (fun x _ => hfderiv_fderiv_bound x)
      convex_univ (Set.mem_univ z) (Set.mem_univ y)
    rw [norm_sub_rev, norm_sub_rev y z] at hmvt
    exact hmvt
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC y)

  have hbound_on_seg :
      ∀ z ∈ segment ℝ y (y - h), ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖h‖ := by
    intro z hz
    have hzy : ‖z - y‖ ≤ ‖h‖ := by
      rw [segment_eq_image' ℝ y (y - h)] at hz
      obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
      simp only [sub_sub_cancel_left]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0, norm_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1
    calc ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖z - y‖ := hinner_mvt z
      _ ≤ C * ‖h‖ := mul_le_mul_of_nonneg_left hzy hC_nonneg

  have houter := (convex_segment y (y - h)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ g z - fderiv ℝ g y)
    (fun z hz => (hΦ_hasFDeriv z).hasFDerivWithinAt)
    hbound_on_seg
    (left_mem_segment ℝ y (y - h))
    (right_mem_segment ℝ y (y - h))
  rw [hΦyh, hΦy, sub_zero] at houter
  calc ‖g (y - h) - g y + (fderiv ℝ g y) h‖
      ≤ C * ‖h‖ * ‖y - h - y‖ := houter
    _ = C * ‖h‖ * ‖h‖ := by rw [sub_sub_cancel_left, norm_neg]
    _ = C * ‖h‖ ^ 2 := by ring


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Taylor remainder estimate in Schwartz seminorms.** The
`(k, n)`-seminorm of the first-order Taylor remainder
`ψ(· - h) - ψ + Dψ · h` is `O(‖h‖²)`, with the implicit constant a fixed
linear combination of `(k, n+2)`-seminorms of `ψ`. -/
theorem seminorm_taylor_remainder_le
    (ψ : 𝓢(E, ℂ)) (k n : ℕ) (h : E) (hh : ‖h‖ ≤ 1) :
    SchwartzMap.seminorm ℂ k n (compSubConstCLM ℂ h ψ - ψ +
      SchwartzMap.evalCLM ℂ E ℂ h (SchwartzMap.fderivCLM ℂ E ℂ ψ)) ≤
      2 ^ k * (Finset.Iic (k, n + 2)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ * ‖h‖ ^ 2 := by sorry

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Schwartz Taylor remainder is `o(h)`.** Pushing the Taylor remainder
through a continuous linear map `L` gives a `o(h)` quantity as `h → 0`,
which is what's needed to establish Fréchet differentiability of
`x ↦ L (ψ(· - x))`. -/
theorem schwartz_taylor_remainder_isLittleO
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : 𝓢(E, ℂ) →L[ℂ] F) (ψ : 𝓢(E, ℂ)) (x₀ : E) :
    (fun h => L (compSubConstCLM ℂ x₀
      (compSubConstCLM ℂ h ψ - ψ +
        SchwartzMap.evalCLM ℂ E ℂ h (SchwartzMap.fderivCLM ℂ E ℂ ψ)))) =o[nhds 0] fun h => h := by

  set R : E → 𝓢(E, ℂ) := fun h => compSubConstCLM ℂ h ψ - ψ +
    SchwartzMap.evalCLM ℂ E ℂ h (SchwartzMap.fderivCLM ℂ E ℂ ψ)

  let q : Seminorm ℂ 𝓢(E, ℂ) := (normSeminorm ℂ F).comp L.toLinearMap
  have hq_cont : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C_L, _, hCL⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq_cont


  let kmax : ℕ := s.sup (fun m => m.1)

  let Kx : ℝ := (1 + ‖x₀‖) ^ kmax * 2 ^ kmax

  let C_ψ : NNReal := s.sup (fun m =>
    (Finset.Iic (m.1, m.2)).sup (fun p =>
      ⟨2 ^ p.1 * (Finset.Iic (p.1, p.2 + 2)).sup
        (fun q' => SchwartzMap.seminorm ℂ q'.1 q'.2) ψ, by positivity⟩))

  let C_total : ℝ := ↑C_L * Kx * ↑C_ψ

  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min 1 (c / (C_total + 1)), by positivity, fun {h} hh => ?_⟩
  rw [dist_zero_right] at hh
  have hh1 : ‖h‖ ≤ 1 := le_trans (le_of_lt hh) (min_le_left _ _)
  have hh_lt : ‖h‖ < c / (C_total + 1) := lt_of_lt_of_le hh (min_le_right _ _)

  have hL_bound : q (compSubConstCLM ℂ x₀ (R h)) ≤
      (C_L • s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x₀ (R h)) :=
    hCL _

  have hsup_Rh : (s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x₀ (R h)) ≤
      Kx * ↑C_ψ * ‖h‖ ^ 2 := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro m hm

    have hTx := TemperedDistributions.SchwartzMap.seminorm_compSubConst_le ℂ m.1 m.2 (R h) x₀

    have hsup_R : (Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) (R h) ≤
        ↑C_ψ * ‖h‖ ^ 2 := by
      apply Seminorm.finset_sup_apply_le (by positivity)
      intro p hp

      have hrem := seminorm_taylor_remainder_le ψ p.1 p.2 h hh1
      have hCψ_le : 2 ^ p.1 * (Finset.Iic (p.1, p.2 + 2)).sup
          (fun q' => SchwartzMap.seminorm ℂ q'.1 q'.2) ψ ≤ ↑C_ψ := by
        have h1 : (⟨2 ^ p.1 * (Finset.Iic (p.1, p.2 + 2)).sup
            (fun q' => SchwartzMap.seminorm ℂ q'.1 q'.2) ψ, by positivity⟩ : NNReal) ≤ C_ψ := by
          apply le_trans (Finset.le_sup (f := fun p : ℕ × ℕ =>
            (⟨2 ^ p.1 * (Finset.Iic (p.1, p.2 + 2)).sup
              (fun q' => SchwartzMap.seminorm ℂ q'.1 q'.2) ψ, by positivity⟩ : NNReal)) hp)
          apply Finset.le_sup (f := fun m : ℕ × ℕ =>
            (Finset.Iic (m.1, m.2)).sup (fun p : ℕ × ℕ =>
              (⟨2 ^ p.1 * (Finset.Iic (p.1, p.2 + 2)).sup
                (fun q' => SchwartzMap.seminorm ℂ q'.1 q'.2) ψ, by positivity⟩ : NNReal))) hm
        exact_mod_cast h1
      linarith [mul_le_mul_of_nonneg_right hCψ_le (by positivity : (0 : ℝ) ≤ ‖h‖ ^ 2)]

    have hm1_le : m.1 ≤ kmax := Finset.le_sup (f := fun m => m.1) hm
    have h1x : 1 ≤ 1 + ‖x₀‖ := le_add_of_nonneg_right (norm_nonneg _)
    calc SchwartzMap.seminorm ℂ m.1 m.2 (compSubConstCLM ℂ x₀ (R h))
        ≤ (1 + ‖x₀‖) ^ m.1 * 2 ^ m.1 *
            (Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) (R h) := hTx
      _ ≤ (1 + ‖x₀‖) ^ m.1 * 2 ^ m.1 * (↑C_ψ * ‖h‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsup_R (by positivity)
      _ ≤ (1 + ‖x₀‖) ^ kmax * 2 ^ kmax * (↑C_ψ * ‖h‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (pow_le_pow_right₀ h1x hm1_le)
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm1_le)
            (by positivity) (by positivity)
      _ = Kx * ↑C_ψ * ‖h‖ ^ 2 := by ring

  have hq_eq : q (compSubConstCLM ℂ x₀ (R h)) = ‖L (compSubConstCLM ℂ x₀ (R h))‖ := rfl
  show ‖L (compSubConstCLM ℂ x₀ (R h))‖ ≤ c * ‖h‖
  have hbound_final : ‖L (compSubConstCLM ℂ x₀ (R h))‖ ≤ C_total * ‖h‖ ^ 2 :=
    calc ‖L (compSubConstCLM ℂ x₀ (R h))‖
        = q (compSubConstCLM ℂ x₀ (R h)) := hq_eq.symm
      _ ≤ (C_L • s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x₀ (R h)) := hL_bound
      _ = ↑C_L * (s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x₀ (R h)) := rfl
      _ ≤ ↑C_L * (Kx * ↑C_ψ * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left hsup_Rh (by positivity)
      _ = C_total * ‖h‖ ^ 2 := by ring


  calc ‖L (compSubConstCLM ℂ x₀ (R h))‖
      ≤ C_total * ‖h‖ ^ 2 := hbound_final
    _ = C_total * ‖h‖ * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hCt_pos : (0 : ℝ) < C_total + 1 := by positivity
        exact le_of_lt (calc C_total * ‖h‖
            ≤ (C_total + 1) * ‖h‖ :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (norm_nonneg _)
          _ < (C_total + 1) * (c / (C_total + 1)) :=
              mul_lt_mul_of_pos_left hh_lt hCt_pos
          _ = c := mul_div_cancel₀ c (ne_of_gt hCt_pos))


/-- **Inductive step for smoothness of `x ↦ L(ψ(· - x))`.** Given that
the same conclusion holds at level `n` for every `ψ`, the function
`x ↦ L(ψ(· - x))` has an `n`-times continuously differentiable derivative
at every point. -/
theorem schwartz_translation_hasFDerivAt_contDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : 𝓢(E, ℂ) →L[ℂ] F) (ψ : 𝓢(E, ℂ)) (n : ℕ)
    (ih : ∀ ψ' : 𝓢(E, ℂ), ContDiff ℝ (↑n) (fun x => L (compSubConstCLM ℂ x ψ'))) :
    ∃ f' : E → (E →L[ℝ] F),
      ContDiff ℝ (↑n) f' ∧ ∀ x, HasFDerivAt (fun x => L (compSubConstCLM ℂ x ψ)) (f' x) x := by
  set ψ' := SchwartzMap.fderivCLM ℂ E ℂ ψ
  set f' : E → (E →L[ℝ] F) := fun x =>
    -({ toFun := fun h => L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ h ψ'))
        map_add' := by
          intro h₁ h₂
          have : SchwartzMap.evalCLM ℂ E ℂ (h₁ + h₂) ψ' =
                 SchwartzMap.evalCLM ℂ E ℂ h₁ ψ' + SchwartzMap.evalCLM ℂ E ℂ h₂ ψ' := by
            ext y; simp only [SchwartzMap.evalCLM_apply_apply, map_add, SchwartzMap.add_apply]
          rw [this, map_add, map_add]
        map_smul' := by
          intro r h
          simp only [RingHom.id_apply]
          have : SchwartzMap.evalCLM ℂ E ℂ (r • h) ψ' =
                 (r : ℂ) • SchwartzMap.evalCLM ℂ E ℂ h ψ' := by
            ext y
            simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.smul_apply, map_smul]; rfl
          rw [this, map_smul, map_smul]; rfl } : E →ₗ[ℝ] F).toContinuousLinearMap
  refine ⟨f', ?_, ?_⟩
  · rw [contDiff_clm_apply_iff]
    intro h
    show ContDiff ℝ ↑n fun x => f' x h
    have hf'eq : (fun x => f' x h) =
        fun x => -L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ h ψ')) := by
      ext x; rfl
    rw [hf'eq]
    exact (ih (SchwartzMap.evalCLM ℂ E ℂ h ψ')).neg
  · intro x₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hrw : ∀ h : E,
        L (compSubConstCLM ℂ (x₀ + h) ψ) - L (compSubConstCLM ℂ x₀ ψ) - f' x₀ h =
        L (compSubConstCLM ℂ x₀
          (compSubConstCLM ℂ h ψ - ψ + SchwartzMap.evalCLM ℂ E ℂ h ψ')) := by
      intro h
      have hcomp : compSubConstCLM ℂ (x₀ + h) ψ =
          compSubConstCLM ℂ x₀ (compSubConstCLM ℂ h ψ) := by
        rw [SchwartzMap.compSubConstCLM_comp]; congr 1; abel
      have hf' : f' x₀ h = -L (compSubConstCLM ℂ x₀ (SchwartzMap.evalCLM ℂ E ℂ h ψ')) := rfl
      rw [hcomp, hf', sub_neg_eq_add, ← map_sub L, ← map_add L,
          ← map_sub (compSubConstCLM ℂ x₀), ← map_add (compSubConstCLM ℂ x₀)]
    simp_rw [hrw]
    exact schwartz_taylor_remainder_isLittleO L ψ x₀

/-- **Smoothness of translation in `Schwartz`.** For any continuous linear
map `L : 𝓢(E, ℂ) →L[ℂ] F`, the map `x ↦ L(φ(· - x))` is `C^∞` on `E`. -/
theorem contDiff_schwartz_translation_clm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : 𝓢(E, ℂ) →L[ℂ] F) (φ : 𝓢(E, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => L (compSubConstCLM ℂ x φ)) := by
  rw [contDiff_infty]
  intro n
  suffices ∀ ψ : 𝓢(E, ℂ), ContDiff ℝ (↑n) (fun x => L (compSubConstCLM ℂ x ψ)) from this φ
  induction n with
  | zero =>
    intro ψ
    simp only [CharP.cast_eq_zero, contDiff_zero]
    exact L.continuous.comp (schwartz_compSubConstCLM_continuous ψ)
  | succ n ih =>
    intro ψ
    have hcast : ((↑(n + 1) : WithTop ℕ∞)) = (↑n : WithTop ℕ∞) + 1 := by push_cast; ring
    rw [hcast, contDiff_succ_iff_hasFDerivAt]
    exact schwartz_translation_hasFDerivAt_contDiff L ψ n ih

/-- **Smoothness of the distributional convolution `v ∗ φ`.** For `v` a
tempered distribution with compact `dsupport` and `φ` Schwartz, the
function `x ↦ v(φ(· - x))` is smooth. -/
theorem contDiff_compactDsupport_convolution_fun
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (φ : 𝓢(E, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => v (compSubConstCLM ℂ x φ)) :=
  contDiff_schwartz_translation_clm v φ


omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in

set_option maxHeartbeats 400000 in

/-- A distribution with compact `dsupport` **vanishes on the complement
of a compact set** (namely `K = dsupport v`). -/
theorem HasCompactDsupport.isVanishingOn_complement
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) :
    ∃ (K : Set E), IsCompact K ∧ Distribution.IsVanishingOn v Kᶜ := by
  refine ⟨dsupport v, hv, ?_⟩


  intro ψ hψ_supp


  suffices h_cs : ∀ (φ : 𝓢(E, ℂ)), HasCompactSupport φ →
      tsupport (⇑φ) ⊆ (dsupport v)ᶜ → v φ = 0 by


    have hclosed : IsClosed {φ : 𝓢(E, ℂ) | v φ = 0} :=
      isClosed_eq v.cont continuous_const
    have hmem : ψ ∈ closure {φ : 𝓢(E, ℂ) | v φ = 0} := by
      apply mem_closure_of_tendsto (f := fun m => bumpCutoffMul m ψ) (b := Filter.atTop)
      · rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ ψ]
        intro ⟨k, j⟩ ε hε
        have h := seminorm_cutoff_sub_tendsto ℂ ψ k j
        rw [Metric.tendsto_atTop] at h
        obtain ⟨N, hN⟩ := h ε hε
        filter_upwards [Filter.Ici_mem_atTop N] with m hm
        simp only [SchwartzMap.schwartzSeminormFamily_apply]
        have h1 := hN m hm
        rw [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at h1
        calc (SchwartzMap.seminorm ℂ k j) (bumpCutoffMul m ψ - ψ)
            = (SchwartzMap.seminorm ℂ k j) (ψ - bumpCutoffMul m ψ) := by
              rw [← map_neg_eq_map]; congr 1; abel
          _ < ε := h1
      · apply Filter.Eventually.of_forall
        intro m
        have hts : tsupport (⇑(bumpCutoffMul m ψ)) ⊆ tsupport (⇑ψ) := by
          apply closure_mono
          intro x hx
          rw [Function.mem_support] at hx ⊢
          intro hψx
          apply hx
          rw [bumpCutoffMul_apply, hψx, smul_zero]
        exact h_cs _ (bumpCutoffMul_hasCompactSupport m ψ) (hts.trans hψ_supp)

    exact hclosed.closure_subset hmem
  classical

  intro φ hφ_compact hφ_supp


  have hclosed_dsupp : IsClosed (dsupport v) := isClosed_dsupport


  let U : E → Set E := fun x =>
    if hx : x ∈ dsupport v then (tsupport (⇑φ))ᶜ
    else (notMem_dsupport_iff x |>.mp hx).choose
  have hU_open : ∀ x, IsOpen (U x) := by
    intro x
    simp only [U]
    split_ifs with hx
    · exact isOpen_compl_iff.mpr (isClosed_tsupport (⇑φ))

    · exact (notMem_dsupport_iff x |>.mp hx).choose_spec.2.1
  have hU_mem : ∀ x, x ∈ U x := by
    intro x
    simp only [U]
    split_ifs with hx
    · exact Set.mem_compl (fun hxφ => absurd hx (hφ_supp hxφ))

    · exact (notMem_dsupport_iff x |>.mp hx).choose_spec.2.2
  have hU_vanish_or_disjoint : ∀ x, IsVanishingOn (⇑v) (U x) ∨ U x ⊆ (tsupport (⇑φ))ᶜ := by
    intro x
    simp only [U]
    split_ifs with hx
    · right; exact Set.Subset.rfl
    · left; exact (notMem_dsupport_iff x |>.mp hx).choose_spec.1

  have hcov : Set.univ ⊆ ⋃ x, U x := fun x _ => Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ E) isClosed_univ U hU_open hcov

  have hlf := ρ.locallyFinite
  have hfin : {i | (Function.support (⇑(ρ i)) ∩ tsupport (⇑φ)).Nonempty}.Finite :=
    hlf.finite_nonempty_inter_compact hφ_compact
  set s := hfin.toFinset with hs_def

  have hρ_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (ρ i : E → ℝ) := by
    intro i; rw [← contMDiff_iff_contDiff]; exact (ρ i).contMDiff

  have hprod_cs : ∀ i, HasCompactSupport (fun x => (↑(ρ i x) : ℂ) * φ x) :=
    fun i => hφ_compact.mul_left
  have hprod_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (↑(ρ i x) : ℂ) * φ x) :=
    fun i => (Complex.ofRealCLM.contDiff.comp (hρ_smooth i)).mul (φ.smooth ⊤)

  let g : E → 𝓢(E, ℂ) := fun i => (hprod_cs i).toSchwartzMap (hprod_smooth i)

  have hg_vanish : ∀ i, v (g i) = 0 := by
    intro i
    cases hU_vanish_or_disjoint i with
    | inl h_van =>

      apply h_van
      calc tsupport ⇑(g i) ⊆ tsupport (ρ i : E → ℝ) := by
              apply closure_mono
              intro x hx
              rw [Function.mem_support] at hx ⊢
              intro hρx; apply hx; rw [(hprod_cs i).toSchwartzMap_toFun (hprod_smooth i)]
              simp [hρx]

           _ ⊆ U i := hρ_sub i
    | inr h_disj =>

      have hg_zero : ∀ x, (g i) x = 0 := by
        intro x
        rw [(hprod_cs i).toSchwartzMap_toFun (hprod_smooth i)]
        by_cases hρ : (ρ i) x = 0
        · simp [hρ]
        ·
          have hx_not_supp : x ∉ tsupport (⇑φ) := by
            have : x ∈ tsupport (ρ i : E → ℝ) :=
              subset_tsupport _ (Function.mem_support.mpr hρ)
            exact h_disj (hρ_sub i this)

          have : φ x = 0 := by
            by_contra h
            exact hx_not_supp (subset_tsupport _ (Function.mem_support.mpr h))
          simp [this]
      have : (g i : 𝓢(E, ℂ)) = 0 := by ext x; exact hg_zero x
      rw [this, map_zero]

  have hφ_eq : φ = ∑ i ∈ s, g i := by
    ext x
    have hsum_app : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x := by
      change (⇑(∑ i ∈ s, g i)) x = _
      simp
    rw [hsum_app]
    have heq : ∀ i, (g i) x = (↑(ρ i x) : ℂ) * φ x :=
      fun i => (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i) x
    simp_rw [heq, ← Finset.sum_mul]
    by_cases hφx : φ x = 0
    · simp [hφx]
    · have hx_supp : x ∈ tsupport (⇑φ) := subset_tsupport _ (Function.mem_support.mpr hφx)
      have hρ_zero : ∀ i, i ∉ s → (ρ i) x = 0 := by
        intro i hi
        by_contra h
        exact hi (hs_def ▸ hfin.mem_toFinset.mpr ⟨x, Function.mem_support.mpr h, hx_supp⟩)
      have hsum_one : ∑ᶠ i, (ρ i) x = 1 := ρ.sum_eq_one (Set.mem_univ x)
      have hsupp : Function.support (fun i => (ρ i) x) ⊆ ↑s := by
        intro i hi
        rw [Finset.mem_coe]
        by_contra hi'
        exact (Function.mem_support.mp hi) (hρ_zero i hi')
      rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum_one
      have hcsum : (∑ i ∈ s, (↑(ρ i x) : ℂ)) = 1 := by
        rw [← Complex.ofReal_one, ← hsum_one]
        simp
      rw [hcsum, one_mul]

  rw [hφ_eq, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hg_vanish i)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Multiplying a Schwartz function by a smooth compactly-supported real
cutoff `χ` produces another Schwartz function `χ · f`. -/
noncomputable def cutoffMul (χ : E → ℝ) (hχcs : HasCompactSupport χ)
    (hχcd : ContDiff ℝ ⊤ χ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (hχcs.smul_right (f' := ⇑f)).toSchwartzMap
    ((hχcd.of_le le_top).smul f.smooth')

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Evaluation lemma for the cutoff product:
`(cutoffMul χ … f) y = χ y • f y`. -/
@[simp]
theorem cutoffMul_apply_eq (χ : E → ℝ) (hχcs : HasCompactSupport χ)
    (hχcd : ContDiff ℝ ⊤ χ) (f : 𝓢(E, ℂ)) (y : E) :
    (cutoffMul χ hχcs hχcd f) y = χ y • f y := by
  unfold cutoffMul
  simp only [HasCompactSupport.toSchwartzMap_toFun]
  exact Complex.real_smul

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Function-level identity for the cutoff product:
`⇑(cutoffMul χ … f) = fun y => χ y • f y`. -/
theorem cutoffMul_coe_eq (χ : E → ℝ) (hχcs : HasCompactSupport χ)
    (hχcd : ContDiff ℝ ⊤ χ) (f : 𝓢(E, ℂ)) :
    ⇑(cutoffMul χ hχcs hχcd f) = fun y => χ y • f y :=
  funext (cutoffMul_apply_eq χ hχcs hχcd f)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Zero-weight Schwartz seminorms are translation-invariant.** Since
`(0, m)`-seminorms involve no polynomial weight, the translated function
`φ(· - x)` has the same `(0, m)`-seminorm as `φ`. -/
theorem seminorm_compSubConst_zero_weight (x : E) (φ : 𝓢(E, ℂ)) (m : ℕ) :
    SchwartzMap.seminorm ℂ 0 m (compSubConstCLM ℂ x φ) = SchwartzMap.seminorm ℂ 0 m φ := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℂ 0 m _ (apply_nonneg _ _)
    intro y
    simp only [pow_zero, one_mul]
    have hc : ⇑(compSubConstCLM ℂ x φ) = fun z => φ (z - x) := by
      ext z; simp [compSubConstCLM_apply]
    rw [hc, iteratedFDeriv_comp_sub]
    have h := le_seminorm ℂ 0 m φ (y - x)
    simp only [pow_zero, one_mul] at h; exact h
  · apply SchwartzMap.seminorm_le_bound ℂ 0 m _ (apply_nonneg _ _)
    intro y
    simp only [pow_zero, one_mul]
    have hc : ⇑(compSubConstCLM ℂ x φ) = fun z => φ (z - x) := by
      ext z; simp [compSubConstCLM_apply]
    have h := le_seminorm ℂ 0 m (compSubConstCLM ℂ x φ) (y + x)
    simp only [pow_zero, one_mul] at h
    rw [hc, iteratedFDeriv_comp_sub, add_sub_cancel_right] at h
    exact h

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
set_option maxHeartbeats 6400000 in
/-- **Cutoff–translation seminorm bound.** Bounded uniformly in the
translation parameter `x`, the `(k, n)`-Schwartz seminorm of the cutoff of
`φ(· - x)` is controlled by a fixed finite supremum of seminorms of `φ`. -/
theorem cutoff_translation_seminorm_bound
    (χ : E → ℝ) (hχcs : HasCompactSupport χ) (hχcd : ContDiff ℝ ⊤ χ) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢(E, ℂ)) (x : E),
      SchwartzMap.seminorm ℂ k n (cutoffMul χ hχcs hχcd (compSubConstCLM ℂ x φ)) ≤
        C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
  let s : Finset (ℕ × ℕ) := (Finset.range (n + 1)).image (fun j => (0, j))

  have hRk : ∃ Rk : ℝ, 0 ≤ Rk ∧ ∀ y ∈ tsupport χ, ‖y‖ ^ k ≤ Rk := by
    by_cases hne : (tsupport χ).Nonempty
    · obtain ⟨y₀, _, hmax⟩ := hχcs.isCompact.exists_isMaxOn hne
        (continuous_norm.pow k).continuousOn
      exact ⟨‖y₀‖ ^ k, by positivity, fun y hy => hmax hy⟩
    · exact ⟨0, le_refl 0, fun y hy =>
        ((Set.not_nonempty_iff_eq_empty.mp hne) ▸ hy).elim⟩
  obtain ⟨Rk, hRk_nn, hRk_bd⟩ := hRk

  have hBi : ∀ i ∈ Finset.range (n + 1),
      ∃ Bi : ℝ, 0 ≤ Bi ∧ ∀ y : E,
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi := by
    intro i _
    have hcsi : HasCompactSupport (iteratedFDeriv ℝ i χ) := hχcs.iteratedFDeriv i
    have hci : Continuous (iteratedFDeriv ℝ i χ) :=
      (hχcd.of_le le_top).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    by_cases hne : (tsupport (iteratedFDeriv ℝ i χ)).Nonempty
    · obtain ⟨z₀, _, hmax⟩ := hcsi.isCompact.exists_isMaxOn hne
        (continuous_norm.comp hci).continuousOn
      refine ⟨(n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ z₀‖, by positivity, fun y => ?_⟩
      gcongr
      by_cases hy : y ∈ tsupport (iteratedFDeriv ℝ i χ)
      · exact hmax hy
      · have : iteratedFDeriv ℝ i χ y = 0 := by
          have : y ∉ Function.support (iteratedFDeriv ℝ i χ) :=
            fun h => hy (subset_tsupport _ h)
          rwa [Function.mem_support, not_not] at this
        simp [this]
    · exact ⟨0, le_refl 0, fun y => by
        rw [Set.not_nonempty_iff_eq_empty] at hne
        have : iteratedFDeriv ℝ i χ y = 0 := by
          have : y ∉ Function.support (iteratedFDeriv ℝ i χ) := by
            intro h; exact (hne ▸ subset_tsupport _ h).elim
          rwa [Function.mem_support, not_not] at this
        simp [this]⟩


  have hBi_exists : ∀ i ∈ Finset.range (n + 1), ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : E, (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ B := hBi

  let Bi' : ℕ → ℝ := fun i =>
    if h : i ∈ Finset.range (n + 1) then (hBi_exists i h).choose else 0
  have hBi'_nn : ∀ i, 0 ≤ Bi' i := by
    intro i; simp only [Bi']; split_ifs with h
    · exact (hBi_exists i h).choose_spec.1
    · exact le_refl 0
  have hBi'_bd : ∀ i ∈ Finset.range (n + 1), ∀ y : E,
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi' i := by
    intro i hi y; simp only [Bi', dif_pos hi]
    exact (hBi_exists i hi).choose_spec.2 y
  let Ctotal : ℝ := Rk * ∑ i ∈ Finset.range (n + 1), Bi' i
  refine ⟨s, Ctotal, ?_, fun φ x => ?_⟩
  · apply mul_nonneg hRk_nn
    exact Finset.sum_nonneg fun i _ => hBi'_nn i
  apply SchwartzMap.seminorm_le_bound ℂ k n
  · exact mul_nonneg (mul_nonneg hRk_nn
      (Finset.sum_nonneg fun i _ => hBi'_nn i)) (apply_nonneg _ _)
  intro y
  rw [cutoffMul_coe_eq]
  set ψ := compSubConstCLM ℂ x φ
  have hχ_cd : ContDiff ℝ ((↑n : ℕ∞) : WithTop ℕ∞) χ := hχcd.of_le le_top
  have hψ_cd : ContDiff ℝ ((↑n : ℕ∞) : WithTop ℕ∞) ψ := by
    apply ψ.smooth'.of_le; exact_mod_cast le_top
  have hsmul_le := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hχ_cd hψ_cd y le_rfl
  by_cases hy_supp : y ∈ tsupport χ
  ·
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => χ z • ψ z) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
            ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
          exact mul_le_mul_of_nonneg_left hsmul_le (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1),
            ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖) *
            ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ i ∈ Finset.range (n + 1),
            Rk * Bi' i * SchwartzMap.seminorm ℂ 0 (n - i) φ := by
          apply Finset.sum_le_sum; intro i hi
          have h1 : ‖y‖ ^ k ≤ Rk := hRk_bd y hy_supp
          have h2 : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi' i := hBi'_bd i hi y
          have h3 : ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ ≤ SchwartzMap.seminorm ℂ 0 (n - i) φ :=
            calc ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖
                ≤ SchwartzMap.seminorm ℂ 0 (n - i) ψ :=
                  SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ψ (n - i) y
              _ = SchwartzMap.seminorm ℂ 0 (n - i) φ :=
                  seminorm_compSubConst_zero_weight x φ (n - i)
          exact mul_le_mul (mul_le_mul h1 h2 (by positivity) hRk_nn)
            h3 (norm_nonneg _) (mul_nonneg hRk_nn (hBi'_nn i))
      _ ≤ ∑ i ∈ Finset.range (n + 1),
            Rk * Bi' i * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
          apply Finset.sum_le_sum; intro i hi
          apply mul_le_mul_of_nonneg_left
          · have hmem : (0, n - i) ∈ s :=
              Finset.mem_image.mpr ⟨n - i, Finset.mem_range.mpr (by omega), rfl⟩
            rw [← SchwartzMap.schwartzSeminormFamily_apply ℂ E ℂ 0 (n - i)]
            exact (Finset.le_sup hmem : schwartzSeminormFamily ℂ E ℂ (0, n - i) ≤ _) φ
          · exact mul_nonneg hRk_nn (hBi'_nn i)
      _ = Ctotal * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
          simp only [Ctotal, Finset.mul_sum]; rw [Finset.sum_mul]
  ·
    have hχ_zero : ∀ i : ℕ, iteratedFDeriv ℝ i χ y = 0 := by
      intro i
      have h1 : y ∉ tsupport (iteratedFDeriv ℝ i χ) :=
        fun h => hy_supp (tsupport_iteratedFDeriv_subset i h)
      have h2 : y ∉ Function.support (iteratedFDeriv ℝ i χ) :=
        fun h => h1 (subset_tsupport _ h)
      rwa [Function.mem_support, not_not] at h2
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => χ z • ψ z) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
            ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
          exact mul_le_mul_of_nonneg_left hsmul_le (by positivity)
      _ = ‖y‖ ^ k * 0 := by
          congr 1; apply Finset.sum_eq_zero; intro i _; simp [hχ_zero i]
      _ ≤ Ctotal * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
          simp only [mul_zero]
          exact mul_nonneg (mul_nonneg hRk_nn
            (Finset.sum_nonneg fun i _ => hBi'_nn i)) (apply_nonneg _ _)


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Schwartz seminorm bound for `v ∗ φ`.** For `v` with compact
distributional support, the `(k, n)`-Schwartz seminorm of the convolution
`x ↦ v(φ(· - x))` is bounded by a fixed sup of seminorms of `φ`. -/
theorem compactDsupportConvolution_seminorm_bound
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (n : ℕ × ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢(E, ℂ)) (x : E),
      ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (fun y => v (compSubConstCLM ℂ y φ)) x‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by


  sorry


/-- Elementary numeric inequality used in `one_add_pow_bound`:
`a + a^N ≤ 1 + a^(N+1)` for `a ≥ 0`. -/
lemma add_pow_nonneg_le_one_add (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    a + a ^ N ≤ 1 + a ^ (N + 1) := by
  suffices h : 0 ≤ (a - 1) * (a ^ N - 1) by nlinarith [pow_succ a N]
  by_cases h : a ≤ 1
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [pow_le_one₀ ha h (n := N)])
  · push Not at h
    exact mul_nonneg (by linarith) (by linarith [one_le_pow₀ h.le (n := N)])


/-- **Polynomial growth lemma.** `(1 + a)^N ≤ 2^N · (1 + a^N)` for
`a ≥ 0`, used to control polynomial weights in Schwartz seminorms. -/
lemma one_add_pow_bound (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc (1 + a) ^ (N + 1) = (1 + a) ^ N * (1 + a) := pow_succ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) * (1 + a) := by gcongr
      _ = 2 ^ N * (1 + a + a ^ N + a ^ N * a) := by ring
      _ = 2 ^ N * (1 + a + a ^ N + a ^ (N + 1)) := by rw [pow_succ]
      _ ≤ 2 ^ N * (2 * (1 + a ^ (N + 1))) := by
          gcongr; linarith [add_pow_nonneg_le_one_add a ha N]
      _ = 2 ^ (N + 1) * (1 + a ^ (N + 1)) := by ring


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Rapid decay of `v ∗ φ`.** For `v` with compact `dsupport`, all
iterated derivatives of `x ↦ v(φ(· - x))` decay faster than any
polynomial. Stated with weight `(1 + ‖x‖)^N`. -/
theorem iteratedFDeriv_compactDsupport_convolution_rapid_decay
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (φ : 𝓢(E, ℂ))
    (N n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (fun x => v (compSubConstCLM ℂ x φ)) x‖ ≤ C := by

  obtain ⟨s₀, C₀, hC₀, h₀⟩ := compactDsupportConvolution_seminorm_bound v hv (0, n)

  obtain ⟨sN, CN, hCN, hN⟩ := compactDsupportConvolution_seminorm_bound v hv (N, n)

  let B₀ := C₀ * (s₀.sup (schwartzSeminormFamily ℂ E ℂ)) φ
  let BN := CN * (sN.sup (schwartzSeminormFamily ℂ E ℂ)) φ
  refine ⟨2 ^ N * (B₀ + BN), ?_, fun x => ?_⟩
  · apply mul_nonneg (by positivity)
    apply add_nonneg
    · exact mul_nonneg hC₀ (apply_nonneg _ _)
    · exact mul_nonneg hCN (apply_nonneg _ _)
  · have hx := norm_nonneg x
    have h0x := h₀ φ x
    simp only [pow_zero, one_mul] at h0x
    have hNx := hN φ x
    calc (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (fun x => v (compSubConstCLM ℂ x φ)) x‖
        ≤ 2 ^ N * (1 + ‖x‖ ^ N) *
          ‖iteratedFDeriv ℝ n (fun x => v (compSubConstCLM ℂ x φ)) x‖ := by
          gcongr
          exact one_add_pow_bound ‖x‖ hx N
      _ = 2 ^ N * (‖iteratedFDeriv ℝ n (fun x => v (compSubConstCLM ℂ x φ)) x‖ +
          ‖x‖ ^ N * ‖iteratedFDeriv ℝ n (fun x => v (compSubConstCLM ℂ x φ)) x‖) := by ring
      _ ≤ 2 ^ N * (B₀ + BN) := by gcongr

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Schwartz decay of `v ∗ φ`.** For `v` with compact `dsupport`, the
function `x ↦ v(φ(· - x))` satisfies the Schwartz decay bounds
`‖x‖^k · ‖∂ⁿ …‖ ≤ C`. -/
theorem decay_compactDsupport_convolution_fun
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (φ : 𝓢(E, ℂ))
    (k n : ℕ) :
    ∃ C : ℝ, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => v (compSubConstCLM ℂ x φ)) x‖ ≤ C := by

  obtain ⟨C, -, hC⟩ := iteratedFDeriv_compactDsupport_convolution_rapid_decay v hv φ k n
  exact ⟨C, fun x => le_trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) k)
    (norm_nonneg _)) (hC x)⟩

/-- The **convolution** of a compactly-`dsupport`-ed tempered distribution
`v` with a Schwartz function `φ`, viewed itself as a Schwartz function:
`(v ∗ φ)(x) := v(φ(· - x))`. -/
def compactDsupportConvolutionSchwartzMap
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  ⟨fun x => v (compSubConstCLM ℂ x φ),
   contDiff_compactDsupport_convolution_fun v hv φ,
   decay_compactDsupport_convolution_fun v hv φ⟩

/-- Evaluation lemma: `(v ∗ φ)(x) = v(φ(· - x))`. -/
@[simp]
theorem compactDsupportConvolutionSchwartzMap_apply
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (φ : 𝓢(E, ℂ)) (x : E) :
    compactDsupportConvolutionSchwartzMap v hv φ x = v (compSubConstCLM ℂ x φ) := rfl

/-- The convolution `(v ∗ ·)` is **additive** in the Schwartz argument. -/
theorem compactDsupportConvolution_map_add
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (φ ψ : 𝓢(E, ℂ)) :
    compactDsupportConvolutionSchwartzMap v hv (φ + ψ) =
    compactDsupportConvolutionSchwartzMap v hv φ +
    compactDsupportConvolutionSchwartzMap v hv ψ := by
  ext x
  show v ((compSubConstCLM ℂ x) (φ + ψ)) =
    v ((compSubConstCLM ℂ x) φ) + v ((compSubConstCLM ℂ x) ψ)
  rw [map_add (compSubConstCLM ℂ x), map_add v]

/-- The convolution `(v ∗ ·)` is **`ℂ`-linear** in the Schwartz argument. -/
theorem compactDsupportConvolution_map_smul
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) (c : ℂ) (φ : 𝓢(E, ℂ)) :
    compactDsupportConvolutionSchwartzMap v hv (c • φ) =
    c • compactDsupportConvolutionSchwartzMap v hv φ := by
  ext x
  show v ((compSubConstCLM ℂ x) (c • φ)) = c • v ((compSubConstCLM ℂ x) φ)
  rw [map_smul (compSubConstCLM ℂ x), map_smul v]

/-- The convolution `φ ↦ v ∗ φ` is a **continuous** map
`𝓢(E, ℂ) → 𝓢(E, ℂ)`, established via boundedness of seminorms. -/
theorem continuous_compactDsupportConvolution
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) :
    Continuous (compactDsupportConvolutionSchwartzMap v hv) := by
  let linMap : 𝓢(E, ℂ) →ₗ[ℂ] 𝓢(E, ℂ) :=
    { toFun := compactDsupportConvolutionSchwartzMap v hv
      map_add' := compactDsupportConvolution_map_add v hv
      map_smul' := compactDsupportConvolution_map_smul v hv }
  show Continuous linMap
  apply WithSeminorms.continuous_of_isBounded
    (schwartz_withSeminorms ℂ E ℂ) (schwartz_withSeminorms ℂ E ℂ)
  apply Seminorm.IsBounded.of_real
  intro ⟨k, n⟩
  obtain ⟨s, C, hC, hbound⟩ := compactDsupportConvolution_seminorm_bound v hv (k, n)
  exact ⟨s, C, fun φ => by
    simp only [schwartzSeminormFamily_apply]
    exact (compactDsupportConvolutionSchwartzMap v hv φ).seminorm_le_bound ℂ k n
      (by positivity) (hbound φ)⟩

/-- **Convolution with a compactly-`dsupport`-ed distribution is a CLM.**
For any such `v`, there exists a continuous linear self-map `T` on
`𝓢(E, ℂ)` with `(T φ) x = v(φ(· - x))`. -/
theorem schwartz_of_compactDsupport_convolution
    (v : 𝓢'(E, ℂ)) (hv : HasCompactDsupport v) :
    ∃ (T : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ)),
      ∀ (φ : 𝓢(E, ℂ)) (x : E),
        (T φ) x = v (compSubConstCLM ℂ x φ) := by
  let linMap : 𝓢(E, ℂ) →ₗ[ℂ] 𝓢(E, ℂ) :=
    { toFun := compactDsupportConvolutionSchwartzMap v hv
      map_add' := compactDsupportConvolution_map_add v hv
      map_smul' := compactDsupportConvolution_map_smul v hv }
  exact ⟨⟨linMap, continuous_compactDsupportConvolution v hv⟩, fun _ _ => rfl⟩

section PolynomialGrowthBound

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Coordinate bound.** Each coordinate of a Euclidean vector is bounded
in absolute value by its norm: `|ξ i| ≤ ‖ξ‖`. -/
lemma EuclideanSpace.abs_coord_le_norm {m : ℕ} (ξ : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    |ξ i| ≤ ‖ξ‖ := by
  have h1 : (ξ i) ^ 2 ≤ ∑ j : Fin m, (ξ j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (ξ j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : ‖ξ‖ ^ 2 = ∑ j : Fin m, (ξ j) ^ 2 := EuclideanSpace.real_norm_sq_eq ξ
  have h3 : (ξ i) ^ 2 ≤ ‖ξ‖ ^ 2 := by linarith
  exact abs_le_of_sq_le_sq h3 (norm_nonneg ξ)

/-- **Polynomial growth bound.** The evaluation of a multivariate
polynomial `Q` of total degree `d` at points of `ℝⁿ` is bounded by a
constant times `(1 + ‖ξ‖)^d`. -/
theorem mvPolynomial_eval_bound (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, C > 0 ∧ ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖MvPolynomial.eval (fun i => ξ i) Q‖ ≤ C * (1 + ‖ξ‖) ^ Q.totalDegree := by
  refine ⟨max 1 (∑ d ∈ Q.support, |Q.coeff d|), by positivity, fun ξ => ?_⟩
  set f : Fin n → ℝ := fun i => ξ i
  have heval : MvPolynomial.eval f Q = ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, f i ^ d i :=
    MvPolynomial.eval_eq' f Q
  rw [heval]
  have h1le : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have hnle : ‖ξ‖ ≤ 1 + ‖ξ‖ := le_add_of_nonneg_left (by norm_num)
  have hmono : ∀ d ∈ Q.support,
      ‖Q.coeff d * ∏ i : Fin n, f i ^ d i‖ ≤
        |Q.coeff d| * (1 + ‖ξ‖) ^ Q.totalDegree := by
    intro d hd
    rw [Real.norm_eq_abs, abs_mul]
    have hprod_bound : |∏ i : Fin n, f i ^ d i| ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by
      rw [Finset.abs_prod]
      have step1 : ∀ i : Fin n, |f i ^ d i| ≤ ‖ξ‖ ^ d i := by
        intro i; rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (EuclideanSpace.abs_coord_le_norm ξ i) _
      have step2 : ∏ i : Fin n, |f i ^ d i| ≤ ∏ i : Fin n, ‖ξ‖ ^ d i :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => step1 i)
      have step3 : ∏ i : Fin n, ‖ξ‖ ^ d i = ‖ξ‖ ^ ∑ i : Fin n, d i :=
        Finset.prod_pow_eq_pow_sum _ _ _
      have step4 : ∑ i : Fin n, d i ≤ Q.totalDegree := by
        have h := MvPolynomial.le_totalDegree hd
        rw [Finsupp.sum_fintype] at h
        · exact h
        · intros; rfl
      calc ∏ i : Fin n, |f i ^ d i|
          ≤ ‖ξ‖ ^ ∑ i : Fin n, d i := step3 ▸ step2
        _ ≤ (1 + ‖ξ‖) ^ ∑ i : Fin n, d i :=
            pow_le_pow_left₀ (norm_nonneg _) hnle _
        _ ≤ (1 + ‖ξ‖) ^ Q.totalDegree :=
            pow_le_pow_right₀ h1le step4
    exact mul_le_mul_of_nonneg_left hprod_bound (abs_nonneg _)
  calc ‖∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, f i ^ d i‖
      ≤ ∑ d ∈ Q.support, ‖Q.coeff d * ∏ i : Fin n, f i ^ d i‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Q.support, (|Q.coeff d| * (1 + ‖ξ‖) ^ Q.totalDegree) :=
        Finset.sum_le_sum hmono
    _ = (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖ξ‖) ^ Q.totalDegree :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ max 1 (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖ξ‖) ^ Q.totalDegree := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _)
        positivity

end PolynomialGrowthBound

section ParametrixSymbol

open Function MvPolynomial

/-- A **smooth function with compact support** automatically belongs to
the Schwartz class; this packages the conversion. -/
theorem compactSupport_contDiff_to_schwartz
    {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) :
    ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∀ ξ, (ψ : EuclideanSpace ℝ (Fin n) → ℂ) ξ = φ ξ :=
  ⟨hφ_supp.toSchwartzMap hφ_smooth,
   fun ξ => hφ_supp.toSchwartzMap_toFun hφ_smooth ξ⟩


/-- **Existence of a parametrix cutoff.** For an elliptic polynomial `P`,
there is a smooth compactly-supported function `φ` equal to `1` exactly on
the (compact) zero set of the symbol `polySymbol n P`. -/
theorem parametrix_cutoff_exists
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ (φ : EuclideanSpace ℝ (Fin n) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      HasCompactSupport φ ∧
      (∀ ξ : EuclideanSpace ℝ (Fin n),
        polySymbol n P ξ ≠ 0 ∨ φ ξ = 1) := by sorry


/-- **Parametrix symbol has temperate growth.** The symbol
`(1 - φ(ξ)) · P(2πiξ)⁻¹`, with `φ` a parametrix cutoff and `P` elliptic,
has temperate growth and is smooth — hence valid as a Fourier multiplier
symbol. -/
theorem parametrix_symbol_hasTemperateGrowth
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_eq_one : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ ≠ 0 ∨ φ ξ = 1) :
    HasTemperateGrowth (fun ξ =>
      (1 - φ ξ) * (polySymbol n P ξ)⁻¹) := by sorry

/-- **Existence of a parametrix symbol for an elliptic operator.** For
elliptic `P`, there is a temperate-growth symbol `Q` and a Schwartz
function `ψ` with `P(2πiξ) · Q(ξ) = 1 - ψ(ξ)`. This is the symbolic
identity behind `P(D) ∘ Q(D) = Id - smoothing`. -/
theorem IsElliptic.parametrix_symbol_exists {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P) (hn : 0 < n) :
    ∃ Q : EuclideanSpace ℝ (Fin n) → ℂ,
      HasTemperateGrowth Q ∧
      ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        ∀ ξ, polySymbol n P ξ * Q ξ = 1 - (ψ : EuclideanSpace ℝ (Fin n) → ℂ) ξ := by

  obtain ⟨φ, hφ_smooth, hφ_supp, hφ_eq_one⟩ := parametrix_cutoff_exists P hP hn

  set Q : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ =>
    (1 - φ ξ) * (polySymbol n P ξ)⁻¹ with hQ_def

  have hQ_temp : HasTemperateGrowth Q :=
    parametrix_symbol_hasTemperateGrowth P hP hn φ hφ_smooth hφ_supp hφ_eq_one

  obtain ⟨ψ, hψ_eq⟩ := compactSupport_contDiff_to_schwartz φ hφ_smooth hφ_supp

  refine ⟨Q, hQ_temp, ψ, fun ξ => ?_⟩
  rw [hψ_eq ξ, hQ_def]
  simp only
  rcases hφ_eq_one ξ with hP_ne | hφ_one
  ·
    rw [mul_comm (polySymbol n P ξ), mul_assoc, inv_mul_cancel₀ hP_ne, mul_one]
  ·
    rw [hφ_one, sub_self, zero_mul, mul_zero]

end ParametrixSymbol

end DifferentialOperators
