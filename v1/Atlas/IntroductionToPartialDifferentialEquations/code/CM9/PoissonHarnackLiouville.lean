/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
import Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenExistence
import Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties

open Set Real MeasureTheory Filter Topology

noncomputable section

namespace PoissonHarnack

/-- The open Euclidean ball $B_R(c) = \{x : \|x - c\| < R\}$ in $\mathbb{R}^n$, using
the Euclidean norm `CM8.euclidNorm`. -/
def euclidBall {n : ℕ} (c : Fin n → ℝ) (R : ℝ) : Set (Fin n → ℝ) :=
  {x | CM8.euclidNorm (x - c) < R}

/-- The Kelvin reflection of $x$ across the sphere $\partial B_R(p) \subset \mathbb{R}^3$:
$x^* = p + \frac{R^2}{|x-p|^2}(x - p)$. This maps the interior of the ball to its exterior
and is used to construct the Green function for a ball. -/
def kelvinReflection (p : Fin 3 → ℝ) (R : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => p i + R ^ 2 * (x i - p i) / CM8.euclidNorm (x - p) ^ 2

/-- The Green function for the ball $B_R(p) \subset \mathbb{R}^3$ defined via the
fundamental solution and its image under Kelvin reflection:
$G(x, y) = \Phi_3(x - y) - \frac{R}{|x-p|}\,\Phi_3(x^* - y)$. -/
def greenBall (R : ℝ) (p x y : Fin 3 → ℝ) : ℝ :=
  CM8.Phi3 (x - y) - (R / CM8.euclidNorm (x - p)) * CM8.Phi3 (kelvinReflection p R x - y)

/-- The componentwise expression for $x^* - y$ where $x^*$ is the Kelvin reflection of $x$. -/
lemma kelvinReflection_sub_eq (p x y : Fin 3 → ℝ) (R : ℝ) :
    kelvinReflection p R x - y =
    fun i => R^2 / CM8.euclidNorm (x - p)^2 * (x i - p i) - (y i - p i) := by
  ext i; simp [kelvinReflection, Pi.sub_apply]; ring

/-- The explicit closed-form expression of `greenBall` for $x \neq p$:
$G(x,y) = -\frac{1}{4\pi|x-y|} + \frac{1}{4\pi}\cdot\frac{R}{|x-p|\,\bigl|\frac{R^2}{|x-p|^2}(x-p)-(y-p)\bigr|}$. -/
noncomputable def greenBallFormula (R : ℝ) (p x y : Fin 3 → ℝ) : ℝ :=
  -1 / (4 * Real.pi * CM8.euclidNorm (x - y)) +
    R / (4 * Real.pi * CM8.euclidNorm (x - p) *
         CM8.euclidNorm (fun i => R^2 / CM8.euclidNorm (x - p)^2 * (x i - p i) - (y i - p i)))

/-- The Green function `greenBall` agrees with the explicit closed form `greenBallFormula`. -/
theorem greenBall_eq_explicit_formula (R : ℝ) (p x y : Fin 3 → ℝ) :
    greenBall R p x y = greenBallFormula R p x y := by
  unfold greenBall greenBallFormula CM8.Phi3
  rw [kelvinReflection_sub_eq]
  ring

/-- The value of the Green function for the ball at the center $p$:
$G(p, y) = -\frac{1}{4\pi|y-p|} + \frac{1}{4\pi R}$. -/
noncomputable def greenBallFormula_at_center (R : ℝ) (p y : Fin 3 → ℝ) : ℝ :=
  -1 / (4 * Real.pi * CM8.euclidNorm (y - p)) + 1 / (4 * Real.pi * R)

section BoundaryVanishHelpers

private def normSq (x : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, x i ^ 2

/-- The standard inner product of two vectors in $\mathbb{R}^3$: $\langle a, b \rangle = \sum_i a_i b_i$. -/
def innerProd3 (a b : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, a i * b i

/-- The square of the Euclidean norm equals the sum of squares: $\|v\|^2 = \sum_i v_i^2$. -/
lemma euclidNorm_sq (v : Fin 3 → ℝ) : CM8.euclidNorm v ^ 2 = normSq v := by
  unfold CM8.euclidNorm normSq; exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Rewrite $\|x^* - \sigma\|^2$ in coordinates using the definition of the Kelvin reflection. -/
lemma normSq_kelvin_sub (p x σ : Fin 3 → ℝ) (R : ℝ) :
    normSq (kelvinReflection p R x - σ) =
    normSq (fun i => p i + R ^ 2 / CM8.euclidNorm (x - p) ^ 2 * (x i - p i) - σ i) := by
  unfold normSq; congr 1; ext i; simp [kelvinReflection, Pi.sub_apply]; ring

/-- Expansion identity: $\|x - \sigma\|^2 = \|x-p\|^2 - 2\langle x-p, \sigma-p\rangle + \|\sigma-p\|^2$. -/
lemma normSq_diff_eq (x σ p : Fin 3 → ℝ) :
    normSq (x - σ) = normSq (x - p) - 2 * innerProd3 (x - p) (σ - p) + normSq (σ - p) := by
  unfold normSq innerProd3; simp only [Fin.sum_univ_three, Pi.sub_apply]; ring

/-- Quadratic expansion: $\|p + c(x-p) - \sigma\|^2 = c^2\|x-p\|^2 - 2c\langle x-p, \sigma-p\rangle + \|\sigma-p\|^2$. -/
lemma normSq_kr_expand (p x σ : Fin 3 → ℝ) (c : ℝ) :
    normSq (fun i => p i + c * (x i - p i) - σ i) =
    c ^ 2 * normSq (x - p) - 2 * c * innerProd3 (x - p) (σ - p) + normSq (σ - p) := by
  unfold normSq innerProd3; simp only [Fin.sum_univ_three, Pi.sub_apply]; ring

/-- Key identity for the Kelvin reflection across the sphere $|\sigma - p| = R$:
$\|x^* - \sigma\|^2 \cdot \|x - p\|^2 = R^2 \cdot \|x - \sigma\|^2$. -/
lemma normSq_product_eq (p x σ : Fin 3 → ℝ) (R : ℝ)
    (hS : normSq (x - p) ≠ 0) (hσ : normSq (σ - p) = R ^ 2) :
    normSq (kelvinReflection p R x - σ) * normSq (x - p) = R ^ 2 * normSq (x - σ) := by
  rw [normSq_kelvin_sub, show R ^ 2 / CM8.euclidNorm (x - p) ^ 2 = R ^ 2 / normSq (x - p) from
    by rw [euclidNorm_sq]]
  rw [normSq_kr_expand, hσ, normSq_diff_eq x σ p, hσ]
  field_simp; ring

/-- The norm form of the Kelvin reflection identity on the sphere $|\sigma - p| = R$:
$\|x^* - \sigma\|\,\|x - p\| = R\,\|x - \sigma\|$. -/
lemma norm_product_identity (p x σ : Fin 3 → ℝ) (R : ℝ) (hR : 0 < R)
    (hxp : 0 < CM8.euclidNorm (x - p)) (hσ : CM8.euclidNorm (σ - p) = R) :
    CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p) =
    R * CM8.euclidNorm (x - σ) := by
  have hS : normSq (x - p) ≠ 0 := by
    intro h; rw [← euclidNorm_sq] at h; nlinarith [sq_nonneg (CM8.euclidNorm (x - p))]
  have hσ2 : normSq (σ - p) = R ^ 2 := by
    have := euclidNorm_sq (σ - p); rw [hσ] at this; linarith
  have h_sq := normSq_product_eq p x σ R hS hσ2

  have lhs_sq : (CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p)) ^ 2 =
      normSq (kelvinReflection p R x - σ) * normSq (x - p) := by
    rw [mul_pow, euclidNorm_sq, euclidNorm_sq]
  have rhs_sq : (R * CM8.euclidNorm (x - σ)) ^ 2 = R ^ 2 * normSq (x - σ) := by
    rw [mul_pow, euclidNorm_sq]
  have lhs_nn : 0 ≤ CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have rhs_nn : 0 ≤ R * CM8.euclidNorm (x - σ) := mul_nonneg (le_of_lt hR) (Real.sqrt_nonneg _)
  nlinarith [sq_abs (CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p)),
             sq_abs (R * CM8.euclidNorm (x - σ)),
             abs_of_nonneg lhs_nn, abs_of_nonneg rhs_nn,
             lhs_sq, rhs_sq, h_sq,
             sq_nonneg (CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p) -
                        R * CM8.euclidNorm (x - σ))]

/-- If $\|a - b\| = 0$ in $\mathbb{R}^3$, then $a = b$ (positive-definiteness of the Euclidean norm). -/
lemma euclidNorm_zero_imp_eq (a b : Fin 3 → ℝ) (h : CM8.euclidNorm (a - b) = 0) :
    a = b := by
  unfold CM8.euclidNorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h
  ext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((a - b) j))).mp h i
    (Finset.mem_univ i)
  simp [Pi.sub_apply] at this; linarith [this]

end BoundaryVanishHelpers

set_option maxHeartbeats 400000 in
/-- Boundary vanishing of the Green function: for $x \in B_R(p)$ with $x \neq p$ and
$\sigma \in \partial B_R(p)$, the Green function $G(x, \sigma) = 0$. -/
theorem greenBall_boundary_vanish (R : ℝ) (hR : 0 < R)
    (p : Fin 3 → ℝ) (x : Fin 3 → ℝ) (σ : Fin 3 → ℝ)
    (hxp : 0 < CM8.euclidNorm (x - p))
    (hx : CM8.euclidNorm (x - p) < R) (hσ : CM8.euclidNorm (σ - p) = R) :
    greenBall R p x σ = 0 := by

  have hd_ne : CM8.euclidNorm (x - p) ≠ 0 := ne_of_gt hxp
  have hxs_ne : CM8.euclidNorm (x - σ) ≠ 0 := by
    intro h
    have heq := euclidNorm_zero_imp_eq x σ h
    subst heq; linarith

  have h_norm := norm_product_identity p x σ R hR hxp hσ

  have hkr_ne : CM8.euclidNorm (kelvinReflection p R x - σ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h_norm
    have : 0 < R * CM8.euclidNorm (x - σ) :=
      mul_pos hR (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne))
    linarith


  unfold greenBall CM8.Phi3
  field_simp
  linarith [h_norm]

/-- The Poisson kernel for the ball $B_R(p) \subset \mathbb{R}^3$:
$P(x, y) = \frac{R^2 - |x-p|^2}{4\pi R\,|x-y|^3}$. This is the negative outward normal
derivative of the Green function on the boundary. -/
def poissonKernel (R : ℝ) (p x y : Fin 3 → ℝ) : ℝ :=
  (R ^ 2 - CM8.euclidNorm (x - p) ^ 2) / (4 * Real.pi * R * CM8.euclidNorm (x - y) ^ 3)

section EuclidBallTopology

/-- The Euclidean norm is a continuous function $\mathbb{R}^n \to \mathbb{R}$. -/
lemma euclidNorm_continuous' {n : ℕ} : Continuous (fun x : Fin n → ℝ => CM8.euclidNorm x) := by
  unfold CM8.euclidNorm
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2))

/-- Each component is bounded by the Euclidean norm: $|x_i| \le \|x\|$. -/
lemma abs_component_le_euclidNorm' {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :

    |x i| ≤ CM8.euclidNorm x := by
  unfold CM8.euclidNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))

/-- The Euclidean norm is absolutely homogeneous: $\|c \cdot x\| = |c|\,\|x\|$. -/
lemma euclidNorm_smul' {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    CM8.euclidNorm (c • x) = |c| * CM8.euclidNorm x := by
  unfold CM8.euclidNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Every point on the sphere $\|z - p\| = R$ lies in the closure of the open ball
$\{w : \|w - p\| < R\}$, witnessed by an explicit approximating sequence. -/
lemma boundary_in_closure' {n : ℕ} (R : ℝ) (hR : 0 < R) (p z : Fin n → ℝ)
    (heq : CM8.euclidNorm (z - p) = R) :
    z ∈ closure {w : Fin n → ℝ | CM8.euclidNorm (w - p) < R} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set M := ‖z - p‖ + 1
  have hM : 0 < M := by positivity
  set δ := min (ε / (2 * M)) (1/2 : ℝ)
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt_1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set w := p + (1 - δ) • (z - p)
  refine ⟨w, ?_, ?_⟩
  · show CM8.euclidNorm (w - p) < R
    have hw_sub : w - p = (1 - δ) • (z - p) := by simp [w, add_sub_cancel_left]
    rw [hw_sub, euclidNorm_smul', heq, abs_of_pos (by linarith : (0 : ℝ) < 1 - δ)]
    nlinarith
  · have hz_sub_w : z - w = δ • (z - p) := by simp [w]; ext i; simp; ring
    calc dist z w = ‖z - w‖ := dist_eq_norm z w
      _ = ‖δ • (z - p)‖ := by rw [hz_sub_w]
      _ = |δ| * ‖z - p‖ := norm_smul δ (z - p)
      _ = δ * ‖z - p‖ := by rw [abs_of_pos hδ_pos]
      _ < δ * M := by nlinarith [norm_nonneg (z - p)]
      _ ≤ (ε / (2 * M)) * M := by nlinarith [min_le_left (ε / (2 * M)) (1/2 : ℝ)]
      _ = ε / 2 := by field_simp
      _ < ε := by linarith

end EuclidBallTopology

/-- The open Euclidean ball in $\mathbb{R}^3$ is a Lipschitz domain (in the sense of
`CM8.IsLipschitzDomain`), which permits the application of integration-by-parts results
to the ball. -/
theorem isLipschitzDomain_euclidBall (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ) :
    CM8.IsLipschitzDomain {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R} := by sorry

/-- The open Euclidean ball $\{z : \|z - p\| < R\}$ is an open set. -/
theorem isOpen_euclidBall (R : ℝ) (p : Fin 3 → ℝ) :
    IsOpen {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R} :=
  (euclidNorm_continuous'.comp (continuous_id.sub continuous_const)).isOpen_preimage _ isOpen_Iio

/-- The open Euclidean ball is bounded in the sense of `Bornology.IsBounded`. -/
theorem isBounded_euclidBall (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ) :
    Bornology.IsBounded {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R} := by
  apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := p) (r := R))
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  simp only [Metric.mem_closedBall]
  rw [dist_pi_le_iff (le_of_lt hR)]
  intro i
  calc dist (z i) (p i) = |z i - p i| := Real.dist_eq _ _
    _ = |(z - p) i| := by simp
    _ ≤ CM8.euclidNorm (z - p) := abs_component_le_euclidNorm' _ i
    _ ≤ R := le_of_lt hz

/-- The topological frontier of the open Euclidean ball is the sphere:
$\partial B_R(p) = \{z : \|z - p\| = R\}$. -/
theorem frontier_euclidBall_eq (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ) :
    frontier {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R} =
    {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) = R} := by
  set f : (Fin 3 → ℝ) → ℝ := fun z => CM8.euclidNorm (z - p)
  set S := {z : Fin 3 → ℝ | f z < R}
  have hf : Continuous f := euclidNorm_continuous'.comp (continuous_id.sub continuous_const)
  have hS_open : IsOpen S := hf.isOpen_preimage _ isOpen_Iio
  have hcl : closure S = {z | f z ≤ R} := by
    ext z; simp only [Set.mem_setOf_eq]; constructor
    · intro hz
      by_contra h; push Not at h
      have : {w | R < f w} ∈ nhds z := (hf.isOpen_preimage _ isOpen_Ioi).mem_nhds h
      obtain ⟨w, hwR, hwS⟩ := mem_closure_iff_nhds.mp hz _ this
      simp only [Set.mem_setOf_eq, S] at hwR hwS; linarith
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact subset_closure hlt
      · exact boundary_in_closure' R hR p z heq
  rw [frontier, interior_eq_iff_isOpen.mpr hS_open, hcl]
  ext z; simp only [Set.mem_diff, Set.mem_setOf_eq, S]; constructor
  · rintro ⟨hle, hlt⟩; linarith
  · intro heq; exact ⟨le_of_eq heq, by linarith⟩

/-- For every $x$ inside the open ball, the fundamental solution $\sigma \mapsto \Phi(x - \sigma)$
is continuous on the sphere (boundary of the ball), since $x \neq \sigma$ on the boundary. -/
theorem fundSolN_continuousOn_frontier_euclidBall (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ) :
    ∀ x ∈ {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R},
    ContinuousOn (fun σ => CM8.FundSolN (x - σ))
      (frontier {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R}) := by
  intro x hx

  have heq : ∀ σ, CM8.FundSolN (x - σ) = CM8.Phi3 (x - σ) := fun σ => CM8.FundSolN_eq_Phi3 (x - σ)
  simp_rw [heq]


  simp only [CM8.Phi3]


  set F := frontier {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R}
  have hF_eq : F = {z | CM8.euclidNorm (z - p) = R} := frontier_euclidBall_eq R hR p

  have hpos : ∀ σ ∈ F, CM8.euclidNorm (x - σ) > 0 := by
    intro σ hσ
    rw [hF_eq] at hσ
    simp only [Set.mem_setOf_eq] at hx hσ

    by_contra h
    push Not at h
    have h0 : CM8.euclidNorm (x - σ) = 0 := le_antisymm h (Real.sqrt_nonneg _)

    have hxσ : x = σ := by
      ext i
      have hsq : ∑ j : Fin 3, (x - σ) j ^ 2 = 0 := by
        unfold CM8.euclidNorm at h0
        exact (Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg _)).mp h0
      have hi : (x - σ) i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((x - σ) j))).mp hsq i
          (Finset.mem_univ _)
      have : (x - σ) i = 0 := sq_eq_zero_iff.mp hi
      simp [Pi.sub_apply] at this; linarith
    rw [hxσ] at hx
    linarith

  have hcont_norm : ContinuousOn (fun σ => CM8.euclidNorm (x - σ)) F :=
    (euclidNorm_continuous'.comp (continuous_const.sub continuous_id)).continuousOn

  have hcont_denom : ContinuousOn (fun σ => 4 * Real.pi * CM8.euclidNorm (x - σ)) F :=
    continuousOn_const.mul hcont_norm
  have hne : ∀ σ ∈ F, 4 * Real.pi * CM8.euclidNorm (x - σ) ≠ 0 := by
    intro σ hσ
    have := hpos σ hσ
    positivity

  exact continuousOn_const.div hcont_denom hne

/-- A harmonic function on the open ball that matches a boundary datum $g$ on $\partial B_R(p)$
extends continuously to the closed ball. -/
theorem harmonic_continuousOn_closure_euclidBall (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ)
    (u g : (Fin 3 → ℝ) → ℝ)
    (hu : CM7.IsHarmonic u {x | CM8.euclidNorm (x - p) < R})
    (hu_bdy : ∀ σ, CM8.euclidNorm (σ - p) = R → u σ = g σ) :
    ContinuousOn u (closure {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R}) := by sorry

/-- Interior $C^2$ regularity of the harmonic corrector $\phi$ extends to the closed ball:
if $\phi(x, \cdot)$ is $C^2$ and harmonic in the open ball, it is $C^2$ on its closure. -/
theorem corrector_contDiffOn_closure_euclidBall (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ)
    (φ : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
    (hφ_c2 : ∀ x ∈ {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R},
      ContDiffOn ℝ 2 (φ x) {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R})
    (hφ_harm : ∀ x ∈ {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R},
      ∀ y ∈ {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R},
      CM8.laplacian (φ x) y = 0) :
    ∀ x ∈ {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R},
    ContDiffOn ℝ 2 (φ x) (closure {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R}) := by sorry

/-- Compatibility between the two formulations of the Laplacian in CM7 and CM8: they
agree definitionally on the same function. -/
lemma laplacian_compat (u : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    CM7.Laplacian 3 u x = CM8.laplacian u x := rfl

/-- Green's representation formula specialised to a ball in $\mathbb{R}^3$: any harmonic
function $u$ on $B_R(p)$ continuous on the closure can be expressed as a surface integral
against the normal derivative of the Green function. -/
theorem green_representation_ball3_axiom (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ)
    (g : (Fin 3 → ℝ) → ℝ)
    (u : (Fin 3 → ℝ) → ℝ)
    (hu_harmonic : CM7.IsHarmonic u {x | CM8.euclidNorm (x - p) < R})
    (hu_bdy : ∀ σ, CM8.euclidNorm (σ - p) = R → u σ = g σ)
    (x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R) :
    ∃ (gf : CM8.GreenFunctionN 3 {z | CM8.euclidNorm (z - p) < R}),
    u x = -(∫ y in {z | CM8.euclidNorm (z - p) < R},
              (0 : ℝ) * gf.G x y) -
          CM8.surfaceIntegral {z | CM8.euclidNorm (z - p) < R}
            (fun σ => g σ * CM8.normalDeriv {z | CM8.euclidNorm (z - p) < R}
              (fun z => gf.G x z) σ) := by

  set Ω : Set (Fin 3 → ℝ) := {z | CM8.euclidNorm (z - p) < R} with hΩ_def

  have hΩ_open : IsOpen Ω := isOpen_euclidBall R p
  have hΩ_bounded : Bornology.IsBounded Ω := isBounded_euclidBall R hR p
  have hΩ_lip : CM8.IsLipschitzDomain Ω := isLipschitzDomain_euclidBall R hR p
  have hΩ_frontier : frontier Ω = {z | CM8.euclidNorm (z - p) = R} :=
    frontier_euclidBall_eq R hR p

  have hΦ_cont := fundSolN_continuousOn_frontier_euclidBall R hR p
  obtain ⟨φ, hφ_c2, hφ_cont, hφ_harm, hφ_bdy, hφ_vanish⟩ :=
    CM8.green_function_decomposition 3 Ω hΩ_open hΩ_bounded hΩ_lip hΦ_cont


  let gf : CM8.GreenFunctionN 3 Ω :=
    { G := fun a b => CM8.FundSolN (a - b) - φ a b
      corrector := φ
      decomposition := fun a b => rfl
      boundary_vanish := fun a ha σ hσ => by
        rw [hΩ_frontier] at hσ
        have := hφ_vanish a (by exact ha) σ (by rw [hΩ_frontier]; exact hσ)
        linarith
      corrector_harmonic := fun a ha b hb =>
        hφ_harm a ha b hb
      corrector_boundary := fun a ha σ hσ =>
        hφ_bdy a ha σ hσ
      corrector_reg := fun a ha => by


        exact corrector_contDiffOn_closure_euclidBall R hR p φ hφ_c2 hφ_harm a ha }

  refine ⟨gf, ?_⟩

  have hx_mem : x ∈ Ω := hx

  have hu_c2 : ContDiffOn ℝ 2 u Ω := CM7.harmonic_is_contDiffOn u Ω hu_harmonic

  have hu_cont : ContinuousOn u (closure Ω) :=
    harmonic_continuousOn_closure_euclidBall R hR p u g hu_harmonic hu_bdy

  have hu_pde : ∀ y ∈ Ω, CM8.laplacian u y = (0 : (Fin 3 → ℝ) → ℝ) y := by
    intro y hy
    rw [← laplacian_compat]
    exact hu_harmonic.laplacian_eq_zero y hy

  have hu_bdy_frontier : ∀ σ ∈ frontier Ω, u σ = g σ := by
    intro σ hσ
    rw [hΩ_frontier] at hσ
    exact hu_bdy σ hσ

  have hPhi_int : MeasureTheory.IntegrableOn
      (fun y => CM8.FundSolN (x - y) * (0 : (Fin 3 → ℝ) → ℝ) y) Ω := by
    simp only [Pi.zero_apply, mul_zero]
    exact MeasureTheory.integrableOn_zero
  have hcorr_int : MeasureTheory.IntegrableOn
      (fun y => gf.corrector x y * (0 : (Fin 3 → ℝ) → ℝ) y) Ω := by
    simp only [Pi.zero_apply, mul_zero]
    exact MeasureTheory.integrableOn_zero

  exact CM8.green_representation Ω gf u (0 : (Fin 3 → ℝ) → ℝ) g
    hΩ_open hΩ_lip hu_c2 hu_cont hu_pde hu_bdy_frontier x hx_mem
    hPhi_int hcorr_int

/-- Existence of the Green function for the ball: an explicit construction packaged as a
`CM8.GreenFunctionN 3` structure. -/
noncomputable def greenBallN_explicit_exists (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ) :
    CM8.GreenFunctionN 3 {z | CM8.euclidNorm (z - p) < R} := by sorry

/-- Uniqueness of the Green function for the ball: any two Green functions for $B_R(p)$
agree at every pair $(x, y)$ with $x$ in the interior. -/
theorem greenFunctionN_ball_unique (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ)
    (gf₁ gf₂ : CM8.GreenFunctionN 3 {z | CM8.euclidNorm (z - p) < R})
    (x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R) (y : Fin 3 → ℝ) :
    gf₁.G x y = gf₂.G x y := by sorry

/-- Formula for the Fréchet derivative of the explicit Green function in the second variable
evaluated on the boundary: $D_y G(x, \sigma) \cdot v = -\frac{1 - |x-p|^2/R^2}{4\pi |x-\sigma|^3}
\sum_i (\sigma_i - p_i) v_i$. -/
theorem fderiv_greenBallN_explicit_eq (R : ℝ) (hR : 0 < R)
    (p x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (fun z => (greenBallN_explicit_exists R hR p).G x z) σ v =
      -(1 - CM8.euclidNorm (x - p) ^ 2 / R ^ 2) / (4 * Real.pi * CM8.euclidNorm (x - σ) ^ 3) *
      (∑ i : Fin 3, (σ i - p i) * v i) := by sorry

/-- Formula for the Fréchet derivative on the boundary for any Green function on the ball
(follows from uniqueness). -/
theorem fderiv_greenFunctionN_ball_eq (R : ℝ) (hR : 0 < R)
    (p x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (gf : CM8.GreenFunctionN 3 {z | CM8.euclidNorm (z - p) < R})
    (σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (fun z => gf.G x z) σ v =
      -(1 - CM8.euclidNorm (x - p) ^ 2 / R ^ 2) / (4 * Real.pi * CM8.euclidNorm (x - σ) ^ 3) *
      (∑ i : Fin 3, (σ i - p i) * v i) := by
  have h_eq : (fun z => gf.G x z) = (fun z => (greenBallN_explicit_exists R hR p).G x z) := by
    ext z; exact greenFunctionN_ball_unique R hR p gf (greenBallN_explicit_exists R hR p) x hx z
  rw [h_eq]
  exact fderiv_greenBallN_explicit_eq R hR p x hx σ hσ v

/-- The outward normal derivative of the Green function on the boundary of the ball equals
the negative of the Poisson kernel: $\partial_{\hat N} G(x, \sigma) = -P(x, \sigma)$. -/
theorem normalDeriv_greenFunctionN_ball_eq_neg_poisson (R : ℝ) (hR : 0 < R)
    (p : Fin 3 → ℝ) (x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (gf : CM8.GreenFunctionN 3 {z | CM8.euclidNorm (z - p) < R})
    (σ : Fin 3 → ℝ) (hσ : σ ∈ frontier {z | CM8.euclidNorm (z - p) < R}) :
    CM8.normalDeriv {z | CM8.euclidNorm (z - p) < R}
      (fun z => gf.G x z) σ = -(poissonKernel R p x σ) := by

  have hσ_eq : CM8.euclidNorm (σ - p) = R := by
    rw [frontier_euclidBall_eq R hR p] at hσ; exact hσ

  show fderiv ℝ (fun z => gf.G x z) σ
    (CM8.outwardUnitNormal {z | CM8.euclidNorm (z - p) < R} σ) = -(poissonKernel R p x σ)

  rw [CM8.outwardUnitNormal_euclidBall_eq R hR p σ hσ_eq]

  rw [fderiv_greenFunctionN_ball_eq R hR p x hx gf σ hσ_eq]

  unfold poissonKernel
  have hR_ne : R ≠ 0 := ne_of_gt hR

  have h_inner : (∑ i : Fin 3, (σ i - p i) * ((σ i - p i) / R)) =
      CM8.euclidNorm (σ - p) ^ 2 / R := by
    unfold CM8.euclidNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have : ∀ i : Fin 3, (σ i - p i) * ((σ i - p i) / R) = (σ - p) i ^ 2 / R := by
      intro i; simp [Pi.sub_apply]; field_simp
    simp_rw [this, Finset.sum_div]
  rw [h_inner, hσ_eq]

  field_simp

/-- The surface integral over the frontier of the open ball equals the surface integral over
the sphere $\|y - p\| = R$. -/
theorem surfaceIntegral_ball_eq_sphere {n : ℕ} (R : ℝ) (hR : 0 < R)
    (p : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    CM8.surfaceIntegral {z | CM8.euclidNorm (z - p) < R} f =
    CM8.surfaceIntegral {y | CM8.euclidNorm (y - p) = R} f := by sorry

/-- Surface integral of $g \cdot \partial_{\hat N} G$ on the sphere equals the negative of
the surface integral of $P(x, \sigma) g(\sigma)$, using
$\partial_{\hat N} G(x, \sigma) = -P(x, \sigma)$. -/
theorem surfaceIntegral_normalDeriv_greenBall3_eq (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ)
    (g : (Fin 3 → ℝ) → ℝ)
    (x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (gf : CM8.GreenFunctionN 3 {z | CM8.euclidNorm (z - p) < R}) :
    CM8.surfaceIntegral {z | CM8.euclidNorm (z - p) < R}
      (fun σ => g σ * CM8.normalDeriv {z | CM8.euclidNorm (z - p) < R}
        (fun z => gf.G x z) σ) =
    -(CM8.surfaceIntegral {y | CM8.euclidNorm (y - p) = R}
      (fun σ => poissonKernel R p x σ * g σ)) := by

  have h_congr : CM8.surfaceIntegral {z | CM8.euclidNorm (z - p) < R}
      (fun σ => g σ * CM8.normalDeriv {z | CM8.euclidNorm (z - p) < R}
        (fun z => gf.G x z) σ) =
      CM8.surfaceIntegral {z | CM8.euclidNorm (z - p) < R}
        (fun σ => -(poissonKernel R p x σ * g σ)) := by
    apply CM8.surfaceIntegral_congr_frontier
    intro σ hσ
    have h_nd := normalDeriv_greenFunctionN_ball_eq_neg_poisson R hR p x hx gf σ hσ
    rw [h_nd]
    ring

  rw [h_congr, surfaceIntegral_ball_eq_sphere R hR p]

  simp only [CM8.surfaceIntegral_eq]
  exact integral_neg _

/-- Auxiliary form of Poisson's formula (Theorem 3.1 in IPDE) combining Green's representation
with the boundary-vanishing properties: for a harmonic $u$ on $B_R(p) \subset \mathbb{R}^3$
with boundary data $g$, $u(x) = \int_{\partial B_R(p)} P(x, \sigma) g(\sigma)\, d\sigma$. -/
theorem poisson_formula_axiom (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ)
    (g : (Fin 3 → ℝ) → ℝ)
    (u : (Fin 3 → ℝ) → ℝ)
    (hu_harmonic : CM7.IsHarmonic u {x | CM8.euclidNorm (x - p) < R})
    (hu_bdy : ∀ σ, CM8.euclidNorm (σ - p) = R → u σ = g σ)
    (x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R) :
    u x = CM8.surfaceIntegral {y | CM8.euclidNorm (y - p) = R}
      (fun σ => poissonKernel R p x σ * g σ) := by

  obtain ⟨gf, h_rep⟩ := green_representation_ball3_axiom R hR p g u hu_harmonic hu_bdy x hx

  have h_vol_zero : -(∫ y in {z | CM8.euclidNorm (z - p) < R}, (0 : ℝ) * gf.G x y) = 0 := by
    simp

  have h_surf := surfaceIntegral_normalDeriv_greenBall3_eq R hR p g x hx gf

  linarith

/-- **Theorem 3.1 (Poisson's formula).** Let $u$ be harmonic on $B_R(p) \subset \mathbb{R}^3$
with continuous boundary values $u(\sigma) = f(\sigma)$ on $\partial B_R(p)$. Then for any
$x \in B_R(p)$,
$u(x) = \frac{R^2 - |x-p|^2}{4\pi R} \int_{\partial B_R(p)} \frac{f(\sigma)}{|x-\sigma|^3}\, d\sigma$. -/
theorem poisson_formula (R : ℝ) (hR : 0 < R) (p : Fin 3 → ℝ)
    (g : (Fin 3 → ℝ) → ℝ)
    (u : (Fin 3 → ℝ) → ℝ)
    (hu_harmonic : CM7.IsHarmonic u {x | CM8.euclidNorm (x - p) < R})
    (hu_bdy : ∀ σ, CM8.euclidNorm (σ - p) = R → u σ = g σ)
    (x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R) :
    u x = CM8.surfaceIntegral {y | CM8.euclidNorm (y - p) = R}
      (fun σ => poissonKernel R p x σ * g σ) :=
  poisson_formula_axiom R hR p g u hu_harmonic hu_bdy x hx

/-- Limit at the center: as $x \to p$ with $x \neq p$, $G(x, y)$ tends to
$-\frac{1}{4\pi|y - p|} + \frac{1}{4\pi R}$ for $y$ on the boundary. (This value is $0$
since $|y - p| = R$.) -/
theorem greenBall_at_center (R : ℝ) (hR : 0 < R) (p y : Fin 3 → ℝ)
    (hy : CM8.euclidNorm (y - p) = R) :
    Filter.Tendsto (fun x => greenBall R p x y)
      (nhdsWithin p {x | 0 < CM8.euclidNorm (x - p)})
      (nhds (-1 / (4 * Real.pi * CM8.euclidNorm (y - p)) + 1 / (4 * Real.pi * R))) := by

  have h_target : -1 / (4 * Real.pi * CM8.euclidNorm (y - p)) + 1 / (4 * Real.pi * R) = 0 := by
    rw [hy]; ring
  rw [h_target]


  apply tendsto_nhds_of_eventually_eq

  rw [eventually_nhdsWithin_iff]

  have hmem : {x : Fin 3 → ℝ | CM8.euclidNorm (x - p) < R} ∈ nhds p := by

    have hcont : Continuous (fun x : Fin 3 → ℝ => CM8.euclidNorm (x - p)) := by
      unfold CM8.euclidNorm
      fun_prop

    apply hcont.isOpen_preimage _ isOpen_Iio |>.mem_nhds
    show CM8.euclidNorm (p - p) < R
    simp only [sub_self]
    unfold CM8.euclidNorm
    simp [hR]

  filter_upwards [hmem] with x' hx' hx'_pos
  exact greenBall_boundary_vanish R hR p x' y hx'_pos hx' hy

/-- Restatement of `greenBall_at_center` in terms of `greenBallFormula_at_center`. -/
theorem greenBall_at_center_eq_formula (R : ℝ) (hR : 0 < R) (p y : Fin 3 → ℝ)
    (hy : CM8.euclidNorm (y - p) = R) :
    Filter.Tendsto (fun x => greenBall R p x y)
      (nhdsWithin p {x | 0 < CM8.euclidNorm (x - p)})
      (nhds (greenBallFormula_at_center R p y)) := by
  exact greenBall_at_center R hR p y hy

/-- The outward unit normal on the sphere $\|σ - p\| = R$ is the radial direction
$\hat N(\sigma) = (\sigma - p) / R$. -/
theorem outwardUnitNormal_ball_spec (R : ℝ) (hR : 0 < R)
    (p σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R) :
    CM8.outwardUnitNormal {y | CM8.euclidNorm (y - p) < R} σ =
      fun i => (σ i - p i) / R :=
  CM8.outwardUnitNormal_euclidBall_eq R hR p σ hσ

/-- Alias for `outwardUnitNormal_ball_spec`: the outward unit normal on the sphere is
$(\sigma - p) / R$. -/
theorem outwardUnitNormal_euclidBall (R : ℝ) (hR : 0 < R)
    (p σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R) :
    CM8.outwardUnitNormal {y | CM8.euclidNorm (y - p) < R} σ =
      fun i => (σ i - p i) / R :=
  outwardUnitNormal_ball_spec R hR p σ hσ

section FDerivPhi3Helpers

/-- Squared Euclidean norm in $\mathbb{R}^3$ as a function: $y \mapsto \sum_j y_j^2$. -/
def normSq3' (y : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, y j ^ 2

/-- Fréchet derivative of `normSq3'` at $x$ packaged as a continuous linear map:
$v \mapsto \sum_j 2 x_j v_j = 2\langle x, v\rangle$. -/
def normSq3_CLM' (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 3, (2 * x j) • ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3) (φ := fun _ => ℝ) j

/-- The squared norm is strictly positive when the underlying vector is nonzero. -/
lemma normSq3_pos' (x : Fin 3 → ℝ) (hx : CM8.euclidNorm x ≠ 0) :
    0 < normSq3' x := by
  unfold normSq3' CM8.euclidNorm at *
  by_contra h; push Not at h
  exact hx (by rw [le_antisymm h (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))]; simp)

/-- `normSq3'` has Fréchet derivative `normSq3_CLM' x` at every point $x \in \mathbb{R}^3$. -/
lemma hasFDerivAt_normSq3' (x : Fin 3 → ℝ) :
    HasFDerivAt normSq3' (normSq3_CLM' x) x := by
  unfold normSq3'
  rw [show (fun y : Fin 3 → ℝ => ∑ j : Fin 3, y j ^ 2) =
      ∑ j : Fin 3, (fun y : Fin 3 → ℝ => y j ^ 2) from by ext y; simp [Finset.sum_apply]]
  apply HasFDerivAt.sum; intro j _
  convert (hasFDerivAt_apply (𝕜 := ℝ) (ι := Fin 3) (F' := fun _ => ℝ) j x).pow 2 using 1
  simp [mul_comm]

/-- Derivative computation: $\frac{d}{ds}\left[-\frac{1}{4\pi\sqrt s}\right] = \frac{1}{8\pi(\sqrt s)^3}$. -/
lemma hasDerivAt_neg_inv_4pi_sqrt (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => -1 / (4 * Real.pi * Real.sqrt s))
      (1 / (8 * Real.pi * (Real.sqrt s) ^ 3)) s := by
  have hsqrt_ne := ne_of_gt (Real.sqrt_pos.mpr hs)
  have h_h : HasDerivAt (fun r => -1 / (4 * Real.pi * r))
    ((-1/(4*Real.pi)) * (-(Real.sqrt s ^ 2)⁻¹)) (Real.sqrt s) := by
    convert (hasDerivAt_inv hsqrt_ne).const_mul (-1/(4*Real.pi)) using 1; ext r; ring
  convert h_h.comp s (Real.hasDerivAt_sqrt (ne_of_gt hs)) using 1
  field_simp; ring

/-- Fréchet derivative of the fundamental solution $\Phi_3$ in $\mathbb{R}^3$ at $y \neq 0$. -/
lemma hasFDerivAt_Phi3_direct (y : Fin 3 → ℝ) (hy : CM8.euclidNorm y ≠ 0) :
    HasFDerivAt CM8.Phi3
      ((1 / (8 * Real.pi * (CM8.euclidNorm y) ^ 3)) • normSq3_CLM' y) y := by
  have h := (hasDerivAt_neg_inv_4pi_sqrt (normSq3' y) (normSq3_pos' y hy)).comp_hasFDerivAt
    y (hasFDerivAt_normSq3' y)
  convert h using 1

/-- The map $y' \mapsto a - y'$ has Fréchet derivative $-\mathrm{id}$ at every point. -/
lemma hasFDerivAt_const_sub_fin3 (a y : Fin 3 → ℝ) :
    HasFDerivAt (fun y' : Fin 3 → ℝ => a - y')
      (-(ContinuousLinearMap.id ℝ (Fin 3 → ℝ))) y := by
  have h1 : HasFDerivAt (fun _ : Fin 3 → ℝ => a) (0 : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) y :=
    hasFDerivAt_const a y
  have h2 : HasFDerivAt (fun y' : Fin 3 → ℝ => y') (ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y :=
    hasFDerivAt_id y
  convert h1.sub h2 using 1; ext v; simp

/-- Chain rule: $\frac{d}{dy'}\Phi_3(a - y')$ at $y$ for $a \neq y$. -/
lemma hasFDerivAt_Phi3_sub_chain (a y : Fin 3 → ℝ)
    (ha : CM8.euclidNorm (a - y) ≠ 0) :
    HasFDerivAt (fun y' => CM8.Phi3 (a - y'))
      (((1 / (8 * Real.pi * (CM8.euclidNorm (a - y)) ^ 3)) • normSq3_CLM' (a - y)).comp
        (-(ContinuousLinearMap.id ℝ (Fin 3 → ℝ)))) y :=
  (hasFDerivAt_Phi3_direct (a - y) ha).comp y (hasFDerivAt_const_sub_fin3 a y)

/-- Explicit action of `normSq3_CLM' x` on a vector $v$: $\sum_j 2 x_j v_j$. -/
lemma normSq3_CLM_apply' (x v : Fin 3 → ℝ) :
    normSq3_CLM' x v = ∑ j : Fin 3, 2 * x j * v j := by
  unfold normSq3_CLM'
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply]

end FDerivPhi3Helpers

/-- Explicit formula for the Fréchet derivative of $y' \mapsto \Phi_3(a - y')$ at $y$,
applied to a direction $v$:
$D\Phi_3(a - \cdot)(y)(v) = -\frac{\langle a - y, v\rangle}{4\pi |a - y|^3}$. -/
theorem fderiv_Phi3_sub_eq (a y : Fin 3 → ℝ) (ha : CM8.euclidNorm (a - y) ≠ 0)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y' => CM8.Phi3 (a - y')) y v =
      -((∑ i : Fin 3, (a i - y i) * v i) / (4 * Real.pi * CM8.euclidNorm (a - y) ^ 3)) := by
  rw [(hasFDerivAt_Phi3_sub_chain a y ha).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
  rw [normSq3_CLM_apply']
  simp only [Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  have h1 : (∑ j : Fin 3, 2 * (a j - y j) * -v j) =
      -2 * (∑ j : Fin 3, (a j - y j) * v j) := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [h1]; ring

/-- $y' \mapsto \Phi_3(a - y')$ is differentiable at $y$ when $a \neq y$. -/
theorem differentiableAt_Phi3_sub (a y : Fin 3 → ℝ) (ha : CM8.euclidNorm (a - y) ≠ 0) :
    DifferentiableAt ℝ (fun y' => CM8.Phi3 (a - y')) y :=
  (hasFDerivAt_Phi3_sub_chain a y ha).differentiableAt

/-- Linearity decomposition of the Fréchet derivative of `greenBall` in the boundary variable:
$D_y G(x, \sigma) v = D_y \Phi_3(x - \sigma) v - \frac{R}{|x-p|} D_y \Phi_3(x^* - \sigma) v$. -/
theorem fderiv_greenBall_decompose (R : ℝ) (hR : 0 < R)
    (p x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (hxp : 0 < CM8.euclidNorm (x - p))
    (σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => greenBall R p x y) σ v =
      fderiv ℝ (fun y => CM8.Phi3 (x - y)) σ v -
      (R / CM8.euclidNorm (x - p)) * fderiv ℝ (fun y => CM8.Phi3 (kelvinReflection p R x - y)) σ v := by

  have hd_ne : CM8.euclidNorm (x - p) ≠ 0 := ne_of_gt hxp
  have hxs_ne : CM8.euclidNorm (x - σ) ≠ 0 := by
    intro h
    have heq := euclidNorm_zero_imp_eq x σ h
    subst heq; linarith
  have h_norm := norm_product_identity p x σ R hR hxp hσ
  have hkr_ne : CM8.euclidNorm (kelvinReflection p R x - σ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h_norm
    have : 0 < R * CM8.euclidNorm (x - σ) :=
      mul_pos hR (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne))
    linarith

  have hd1 : DifferentiableAt ℝ (fun y => CM8.Phi3 (x - y)) σ :=
    differentiableAt_Phi3_sub x σ hxs_ne
  have hd2 : DifferentiableAt ℝ (fun y => CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    differentiableAt_Phi3_sub (kelvinReflection p R x) σ hkr_ne

  have hfg : (fun y => greenBall R p x y) =
    (fun y => CM8.Phi3 (x - y) - R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) := by
    ext y; simp [greenBall]
  rw [hfg]

  have hcg : DifferentiableAt ℝ (fun y => R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    hd2.const_mul _
  have key : fderiv ℝ (fun y => CM8.Phi3 (x - y) - R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ =
    fderiv ℝ (fun y => CM8.Phi3 (x - y)) σ - fderiv ℝ (fun y => R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    (hd1.hasFDerivAt.sub hcg.hasFDerivAt).fderiv
  rw [key]
  simp only [ContinuousLinearMap.sub_apply]
  congr 1
  have hconst : fderiv ℝ (fun y => R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ =
    (R / CM8.euclidNorm (x - p)) • fderiv ℝ (fun y => CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    (hd2.hasFDerivAt.const_mul _).fderiv
  rw [hconst, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Explicit formula for the Fréchet derivative of `greenBall` in the boundary variable:
$D_y G(x, \sigma) v = \frac{1 - |x-p|^2/R^2}{4\pi |x - \sigma|^3} \sum_i (\sigma_i - p_i) v_i$. -/
theorem fderiv_greenBall_eq (R : ℝ) (hR : 0 < R)
    (p x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (hxp : 0 < CM8.euclidNorm (x - p))
    (σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => greenBall R p x y) σ v =
      (1 - CM8.euclidNorm (x - p) ^ 2 / R ^ 2) / (4 * Real.pi * CM8.euclidNorm (x - σ) ^ 3) *
      (∑ i : Fin 3, (σ i - p i) * v i) := by

  rw [fderiv_greenBall_decompose R hR p x hx hxp σ hσ v]

  have hd_ne : CM8.euclidNorm (x - p) ≠ 0 := ne_of_gt hxp
  have hxs_ne : CM8.euclidNorm (x - σ) ≠ 0 := by
    intro h
    have heq := euclidNorm_zero_imp_eq x σ h
    subst heq; linarith
  have h_norm := norm_product_identity p x σ R hR hxp hσ
  have hkr_ne : CM8.euclidNorm (kelvinReflection p R x - σ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h_norm
    have : 0 < R * CM8.euclidNorm (x - σ) :=
      mul_pos hR (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne))
    linarith

  rw [fderiv_Phi3_sub_eq x σ hxs_ne v]
  rw [fderiv_Phi3_sub_eq (kelvinReflection p R x) σ hkr_ne v]

  set d := CM8.euclidNorm (x - p) with hd_def
  set e := CM8.euclidNorm (x - σ) with he_def
  set k := CM8.euclidNorm (kelvinReflection p R x - σ) with hk_def

  have hR_ne : R ≠ 0 := ne_of_gt hR
  have he_pos : 0 < e := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne)
  have hk_pos : 0 < k := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hkr_ne)

  have h_kr_comp : ∀ i : Fin 3,
      kelvinReflection p R x i - σ i = R ^ 2 / d ^ 2 * (x i - p i) - (σ i - p i) := by
    intro i; simp [kelvinReflection]; ring
  have h_kr_sum : (∑ i : Fin 3, (kelvinReflection p R x i - σ i) * v i) =
      R ^ 2 / d ^ 2 * (∑ i : Fin 3, (x i - p i) * v i) - ∑ i : Fin 3, (σ i - p i) * v i := by
    simp_rw [h_kr_comp]; simp only [Fin.sum_univ_three]; ring

  have h_xs_sum : (∑ i : Fin 3, (x i - σ i) * v i) =
      (∑ i : Fin 3, (x i - p i) * v i) - ∑ i : Fin 3, (σ i - p i) * v i := by
    simp only [Fin.sum_univ_three]; ring
  rw [h_kr_sum, h_xs_sum]


  set Sxp := ∑ i : Fin 3, (x i - p i) * v i with hSxp_def
  set Ssp := ∑ i : Fin 3, (σ i - p i) * v i with hSsp_def


  have hk_eq : k = R * e / d := by
    field_simp; linarith [h_norm]
  have hk3_eq : k ^ 3 = R ^ 3 * e ^ 3 / d ^ 3 := by
    rw [hk_eq]; field_simp
  rw [hk3_eq]

  have he_ne : e ≠ 0 := ne_of_gt he_pos
  have h4pie3 : (4 : ℝ) * π * e ^ 3 ≠ 0 := by positivity
  field_simp
  ring

/-- The outward normal derivative of the explicit `greenBall` on the sphere equals the
Poisson kernel: $\partial_{\hat N(\sigma)} G(x, \sigma) = \frac{R^2 - |x-p|^2}{4\pi R\, |x-\sigma|^3}$. -/
theorem greenBall_normal_deriv_eq_poisson (R : ℝ) (hR : 0 < R)
    (p x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (hxp : 0 < CM8.euclidNorm (x - p))
    (σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R) :
    CM8.normalDeriv {y | CM8.euclidNorm (y - p) < R}
      (fun y => greenBall R p x y) σ = poissonKernel R p x σ := by

  unfold CM8.normalDeriv

  rw [outwardUnitNormal_euclidBall R hR p σ hσ]

  rw [fderiv_greenBall_eq R hR p x hx hxp σ hσ]

  unfold poissonKernel

  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hR2_ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR_ne

  have h_inner : (∑ i : Fin 3, (σ i - p i) * ((σ i - p i) / R)) =
      CM8.euclidNorm (σ - p) ^ 2 / R := by
    unfold CM8.euclidNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have : ∀ i : Fin 3, (σ i - p i) * ((σ i - p i) / R) = (σ - p) i ^ 2 / R := by
      intro i; simp [Pi.sub_apply]; field_simp
    simp_rw [this, Finset.sum_div]
  rw [h_inner, hσ]


  field_simp

/-- **Lemma 2.0.1 (Green function for the ball).** Combined statement of the four
characterising properties of the Green function for a ball $B_R(p) \subset \mathbb{R}^3$:
(i) the explicit closed-form formula; (ii) boundary vanishing $G(x, \sigma) = 0$ for
$\sigma \in \partial B_R(p)$; (iii) the value at the center; (iv) the normal derivative on
the boundary equals the Poisson kernel. -/
theorem lemma_2_0_1_green_ball (R : ℝ) (hR : 0 < R)
    (p x : Fin 3 → ℝ) (hx : CM8.euclidNorm (x - p) < R)
    (hxp : 0 < CM8.euclidNorm (x - p))
    (σ : Fin 3 → ℝ) (hσ : CM8.euclidNorm (σ - p) = R) :

    (greenBall R p x σ = greenBallFormula R p x σ) ∧

    (greenBall R p x σ = 0) ∧

    (Filter.Tendsto (fun z => greenBall R p z σ)
      (nhdsWithin p {z | 0 < CM8.euclidNorm (z - p)})
      (nhds (greenBallFormula_at_center R p σ))) ∧

    (CM8.normalDeriv {y | CM8.euclidNorm (y - p) < R}
      (fun y => greenBall R p x y) σ = poissonKernel R p x σ) :=
  ⟨greenBall_eq_explicit_formula R p x σ,
   greenBall_boundary_vanish R hR p x σ hxp hx hσ,
   greenBall_at_center_eq_formula R hR p σ hσ,
   greenBall_normal_deriv_eq_poisson R hR p x hx hxp σ hσ⟩

/-- The natural identification of a tuple $v : \mathrm{Fin}\,n \to \mathbb{R}$ with an
element of the $\ell^2$ norm space `PiLp 2 (fun _ => ℝ)`. -/
def toPiLp {n : ℕ} (v : Fin n → ℝ) : PiLp 2 (fun _ : Fin n => ℝ) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm v

/-- The Euclidean norm agrees with the canonical $\ell^2$ norm on `PiLp 2`. -/
lemma euclidNorm_eq_piLp_norm {n : ℕ} (v : Fin n → ℝ) :
    CM8.euclidNorm v = ‖toPiLp v‖ := by
  unfold CM8.euclidNorm toPiLp
  rw [PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [WithLp.equiv, Real.norm_eq_abs, sq_abs]

/-- Triangle inequality for the Euclidean norm: $\|a - b\| \le \|a\| + \|b\|$. -/
lemma euclidNorm_sub_le {n : ℕ} (a b : Fin n → ℝ) :
    CM8.euclidNorm (a - b) ≤ CM8.euclidNorm a + CM8.euclidNorm b := by
  rw [euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm]
  have h : toPiLp (a - b) = toPiLp a - toPiLp b := by
    unfold toPiLp; simp [WithLp.equiv]
  rw [h]; exact norm_sub_le (toPiLp a) (toPiLp b)

/-- Reverse triangle inequality: $\|\sigma\| - \|x\| \le \|x - \sigma\|$. -/
lemma euclidNorm_reverse_triangle {n : ℕ} (x σ : Fin n → ℝ) :
    CM8.euclidNorm σ - CM8.euclidNorm x ≤ CM8.euclidNorm (x - σ) := by
  rw [euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm]
  have h : toPiLp (x - σ) = toPiLp x - toPiLp σ := by
    unfold toPiLp; simp [WithLp.equiv]
  rw [h]
  have := abs_le.mp (abs_norm_sub_norm_le (toPiLp x) (toPiLp σ))
  linarith [this.2]

/-- Upper bound for the distance from $x$ to a point on the sphere of radius $R$:
$\|x - \sigma\| \le R + \|x\|$. -/
lemma distance_upper_bound_on_sphere {n : ℕ} (x σ : Fin n → ℝ) (R : ℝ)
    (hσ : CM8.euclidNorm σ = R) :
    CM8.euclidNorm (x - σ) ≤ R + CM8.euclidNorm x := by
  calc CM8.euclidNorm (x - σ)
      ≤ CM8.euclidNorm x + CM8.euclidNorm σ := euclidNorm_sub_le x σ
    _ = CM8.euclidNorm x + R := by rw [hσ]
    _ = R + CM8.euclidNorm x := by ring

/-- Lower bound for the distance from $x$ to a point on the sphere of radius $R$:
$R - \|x\| \le \|x - \sigma\|$. -/
lemma distance_lower_bound_on_sphere {n : ℕ} (x σ : Fin n → ℝ) (R : ℝ)
    (hσ : CM8.euclidNorm σ = R) :
    R - CM8.euclidNorm x ≤ CM8.euclidNorm (x - σ) := by
  calc R - CM8.euclidNorm x = CM8.euclidNorm σ - CM8.euclidNorm x := by rw [hσ]
    _ ≤ CM8.euclidNorm (x - σ) := euclidNorm_reverse_triangle x σ

/-- For a non-negative harmonic function $u$ on $B_R(0)$, there exists a non-negative weight
$W \ge 0$ such that $u(x) = (R^2 - |x|^2) W$. This packages the positivity of $u(x)$ and the
positivity of $R^2 - |x|^2$ inside the ball. -/
theorem poisson_representation_weight_axiom {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (_hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R) :
    ∃ W : ℝ, 0 ≤ W ∧
    u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by

  have hx_mem : CM8.euclidNorm (x - 0) < R := hx
  simp only [sub_zero] at hx_mem
  have hNorm_nonneg : 0 ≤ CM8.euclidNorm x := by
    unfold CM8.euclidNorm; exact Real.sqrt_nonneg _
  have hR2_pos : R ^ 2 - CM8.euclidNorm x ^ 2 > 0 := by
    have : CM8.euclidNorm x ^ 2 < R ^ 2 := by
      apply sq_lt_sq'
      · linarith
      · exact hx_mem
    linarith
  refine ⟨u x / (R ^ 2 - CM8.euclidNorm x ^ 2), ?_, ?_⟩
  · exact div_nonneg (hu_nonneg x hx) (le_of_lt hR2_pos)
  · field_simp

/-- Primitive lower bound: given a uniform upper bound $\|x - \sigma\| \le d$ for $\sigma$ on
the sphere, we have $\frac{R^{n-2}(R^2 - |x|^2)}{d^n}\, u(0) \le u(x)$. This bound is the
starting point of the Harnack inequality argument. -/
theorem poisson_integral_lower_bound_primitive {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by sorry

/-- Helper deriving a lower bound on the Poisson weight $W$ from
`poisson_integral_lower_bound_primitive` and the representation $u(x) = (R^2-|x|^2) W$. -/
theorem poisson_weight_lower_bound_from_surface_monotonicity_MVP_helper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_nn : 0 ≤ W) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W := by

  have h_int := poisson_integral_lower_bound_primitive u R hR hu_harmonic
    hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Mean-value type lower bound: $\frac{R^{n-2}(R^2 - |x|^2)}{d^n}\, u(0) \le u(x)$ when
$\|x - \sigma\| \le d$ for all $\sigma$ on the sphere. -/
theorem poisson_integral_lower_bound_from_surface_monotonicity_MVP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_lb := poisson_weight_lower_bound_from_surface_monotonicity_MVP_helper
    u R hR hu_harmonic hu_nonneg x hx W hW_nn hW_eq d hd hd_bound

  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_lt : CM8.euclidNorm x < R := by
      have : CM8.euclidNorm (x - 0) < R := hx
      simp only [sub_zero] at this
      exact this
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Variant of `poisson_weight_lower_bound_from_surface_monotonicity_MVP_helper`: the same
lower bound $R^{n-2}u(0)/d^n \le W$ on the Poisson weight. -/
theorem poisson_weight_lower_bound_kernel_MVP_axiom {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (_hW_nn : 0 ≤ W) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W := by

  have h_int := poisson_integral_lower_bound_from_surface_monotonicity_MVP u R hR hu_harmonic
    hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Fundamental form of the Poisson integral lower bound derived from the weight bound. -/
theorem poisson_integral_lower_bound_fundamental {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_lb := poisson_weight_lower_bound_kernel_MVP_axiom u R hR hu_harmonic hu_nonneg x hx
    W hW_nn hW_eq d hd hd_bound

  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_lt : CM8.euclidNorm x < R := by
      have : CM8.euclidNorm (x - 0) < R := hx
      simp only [sub_zero] at this; exact this
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Core helper specialisation of the Poisson integral lower bound. -/
theorem poisson_integral_lower_bound_core_helper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x :=
  poisson_integral_lower_bound_fundamental u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

/-- Core lower bound on the Poisson weight $W$ given $\|x - \sigma\| \le d$ on the sphere. -/
theorem poisson_weight_lower_bound_core {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W) (_hW_nn : 0 ≤ W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W := by

  have h_int := poisson_integral_lower_bound_core_helper u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Core version of the Poisson integral lower bound combining the weight bound and the
representation $u(x) = (R^2 - |x|^2) W$. -/
theorem poisson_integral_lower_bound_surface_monotonicity_MVP_core {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_lb := poisson_weight_lower_bound_core u R hR hu_harmonic hu_nonneg x hx W hW_eq hW_nn d hd hd_bound

  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_lt : CM8.euclidNorm x < R := by
      have : CM8.euclidNorm (x - 0) < R := hx
      simp only [sub_zero] at this; exact this
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Direct version of the Poisson weight lower bound: $R^{n-2} u(0) / d^n \le W$. -/
theorem poisson_weight_lower_bound_surface_monotonicity_MVP_direct {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W) (_hW_nn : 0 ≤ W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W := by

  have h_int := poisson_integral_lower_bound_surface_monotonicity_MVP_core u R hR hu_harmonic
    hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Mean-value type lower bound for the Poisson integral derived from surface monotonicity. -/
theorem poisson_integral_lower_bound_surface_monotonicity_MVP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_lb := poisson_weight_lower_bound_surface_monotonicity_MVP_direct u R hR hu_harmonic
    hu_nonneg x hx W hW_eq hW_nn d hd hd_bound

  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_lt : CM8.euclidNorm x < R := by
      have : CM8.euclidNorm (x - 0) < R := hx
      simp only [sub_zero] at this; exact this
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Alias for `poisson_weight_lower_bound_surface_monotonicity_MVP_direct`, expressing the
lower bound $R^{n-2} u(0) / d^n \le W$. -/
theorem poisson_weight_bound_from_surface_integral_MVP_lower {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W) (_hW_nn : 0 ≤ W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W :=
  poisson_weight_lower_bound_surface_monotonicity_MVP_direct u R hR hu_harmonic
    hu_nonneg x hx W hW_eq _hW_nn d hd hd_bound

/-- Poisson-formula style lower bound consequence:
$\frac{R^{n-2}(R^2 - |x|^2)}{d^n} u(0) \le u(x)$ when $\|x - \sigma\| \le d$. -/
theorem poisson_formula_monotonicity_MVP_lower {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx


  have hW_lb := poisson_weight_bound_from_surface_integral_MVP_lower u R hR hu_harmonic
    hu_nonneg x hx W hW_eq hW_nn d hd hd_bound


  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Upper-bound counterpart: if $d \le \|x - \sigma\|$ for all $\sigma$ on the sphere,
then $W \le R^{n-2} u(0) / d^n$. -/
theorem poisson_weight_upper_bound_from_surface_monotonicity_MVP_helper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_nn : 0 ≤ W) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    W ≤ R ^ (n - 2) * u 0 / d ^ n := by sorry

/-- Upper bound: $u(x) \le \frac{R^{n-2}(R^2 - |x|^2)}{d^n} u(0)$ when
$d \le \|x - \sigma\|$ on the sphere. -/
theorem poisson_integral_upper_bound_from_surface_monotonicity_MVP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_ub := poisson_weight_upper_bound_from_surface_monotonicity_MVP_helper
    u R hR hu_harmonic hu_nonneg x hx W hW_nn hW_eq d hd hd_bound

  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_lt : CM8.euclidNorm x < R := by
      have : CM8.euclidNorm (x - 0) < R := hx
      simp only [sub_zero] at this
      exact this
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc (R ^ 2 - CM8.euclidNorm x ^ 2) * W
      ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by
        apply mul_le_mul_of_nonneg_left hW_ub hR2_sub
    _ = R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by ring

/-- Fundamental upper bound on the Poisson weight derived from `poisson_integral_upper_bound_from_surface_monotonicity_MVP`. -/
theorem poisson_weight_upper_bound_fundamental {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    W ≤ R ^ (n - 2) * u 0 / d ^ n := by

  have h_int := poisson_integral_upper_bound_from_surface_monotonicity_MVP u R hR hu_harmonic
    hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x)]


  have h1 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Fundamental upper bound: $u(x) \le \frac{R^{n-2}(R^2 - |x|^2)}{d^n} u(0)$. -/
theorem poisson_integral_upper_bound_fundamental {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by
  obtain ⟨W, _, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx
  have hW_ub := poisson_weight_upper_bound_fundamental u R hR hu_harmonic hu_nonneg x hx
    W hW_eq d hd hd_bound
  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this
    exact this
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc (R ^ 2 - CM8.euclidNorm x ^ 2) * W
      ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) :=
        mul_le_mul_of_nonneg_left hW_ub hR2_sub
    _ = R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by ring

/-- Core helper specialisation of the Poisson integral upper bound. -/
theorem poisson_integral_upper_bound_core_helper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 :=
  poisson_integral_upper_bound_fundamental u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

/-- Core upper bound on the Poisson weight $W \le R^{n-2} u(0) / d^n$. -/
theorem poisson_weight_upper_bound_core {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W) (_hW_nn : 0 ≤ W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    W ≤ R ^ (n - 2) * u 0 / d ^ n := by
  have h_int := poisson_integral_upper_bound_core_helper u R hR hu_harmonic hu_nonneg x hx d hd hd_bound
  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  have h1 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Core MVP-style version of the Poisson integral upper bound combining weight and
representation steps. -/
theorem poisson_integral_upper_bound_surface_monotonicity_MVP_core {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_ub := poisson_weight_upper_bound_core u R hR hu_harmonic hu_nonneg x hx W hW_eq hW_nn d hd hd_bound

  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    have hx_lt : CM8.euclidNorm x < R := by
      have : CM8.euclidNorm (x - 0) < R := hx
      simp only [sub_zero] at this; exact this
    have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc (R ^ 2 - CM8.euclidNorm x ^ 2) * W
      ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by
        apply mul_le_mul_of_nonneg_left hW_ub hR2_sub
    _ = R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by ring

/-- Direct version of the Poisson weight upper bound: $W \le R^{n-2} u(0) / d^n$. -/
theorem poisson_weight_upper_bound_surface_monotonicity_MVP_direct {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W) (_hW_nn : 0 ≤ W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    W ≤ R ^ (n - 2) * u 0 / d ^ n := by

  have h_int := poisson_integral_upper_bound_surface_monotonicity_MVP_core u R hR hu_harmonic
    hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]


  have h1 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Alias for `poisson_weight_upper_bound_surface_monotonicity_MVP_direct`. -/
theorem poisson_weight_bound_from_surface_integral_MVP_upper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W) (_hW_nn : 0 ≤ W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    W ≤ R ^ (n - 2) * u 0 / d ^ n :=
  poisson_weight_upper_bound_surface_monotonicity_MVP_direct u R hR hu_harmonic
    hu_nonneg x hx W hW_eq _hW_nn d hd hd_bound

/-- Poisson-formula style upper bound consequence: $u(x) \le \frac{R^{n-2}(R^2-|x|^2)}{d^n} u(0)$. -/
theorem poisson_formula_monotonicity_MVP_upper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx


  have hW_ub := poisson_weight_bound_from_surface_integral_MVP_upper u R hR hu_harmonic
    hu_nonneg x hx W hW_eq hW_nn d hd hd_bound


  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp only [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc (R ^ 2 - CM8.euclidNorm x ^ 2) * W
      ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by
        apply mul_le_mul_of_nonneg_left hW_ub hR2_sub
    _ = R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by ring

/-- Helper alias for the Poisson integral lower bound. -/
lemma poisson_integral_lower_bound_surfaceIntegral_helper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x :=
  poisson_formula_monotonicity_MVP_lower u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

/-- Lower bound on the Poisson weight $W$ derived from the kernel-based mean-value bound. -/
theorem poisson_weight_lower_bound_from_kernel_MVP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W := by

  have h_int := poisson_integral_lower_bound_surfaceIntegral_helper u R hR hu_harmonic
    hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Helper alias for the Poisson integral upper bound. -/
lemma poisson_integral_upper_bound_surfaceIntegral_helper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 :=
  poisson_formula_monotonicity_MVP_upper u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

/-- Upper bound on the Poisson weight $W$ derived from the kernel-based mean-value bound. -/
theorem poisson_weight_upper_bound_from_kernel_MVP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    W ≤ R ^ (n - 2) * u 0 / d ^ n := by

  have h_int := poisson_integral_upper_bound_surfaceIntegral_helper u R hR hu_harmonic
    hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Poisson integral lower bound derived from the mean-value property. -/
theorem poisson_integral_lower_bound_from_MVP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_lb := poisson_weight_lower_bound_from_kernel_MVP u R hR hu_harmonic hu_nonneg x hx
    W hW_eq d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Poisson integral upper bound derived from the mean-value property. -/
theorem poisson_integral_upper_bound_from_MVP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_ub := poisson_weight_upper_bound_from_kernel_MVP u R hR hu_harmonic hu_nonneg x hx
    W hW_eq d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc (R ^ 2 - CM8.euclidNorm x ^ 2) * W
      ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by
        apply mul_le_mul_of_nonneg_left hW_ub hR2_sub
    _ = R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by ring

/-- Lower bound on the Poisson weight $W$ derived from the integral monotonicity bound. -/
theorem poisson_weight_lower_bound_from_integral_monotonicity {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW_eq : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W) (_hW_nn : 0 ≤ W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W := by

  have h_int := poisson_integral_lower_bound_from_MVP u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Axiomatic form of the Poisson integral lower bound used in the Harnack inequality chain. -/
theorem poisson_integral_lower_bound_axiom {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_lb := poisson_weight_lower_bound_from_integral_monotonicity u R hR hu_harmonic hu_nonneg x hx W hW_eq hW_nn d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]
  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Axiomatic form of the Poisson weight lower bound. -/
theorem poisson_weight_lower_bound_axiom {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * u 0 / d ^ n ≤ W := by

  have h_int := poisson_integral_lower_bound_axiom u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  have h_ring : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Axiomatic form of the Poisson weight upper bound. -/
theorem poisson_weight_upper_bound_axiom {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (W : ℝ) (hW : u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    W ≤ R ^ (n - 2) * u 0 / d ^ n := by

  have h_int := poisson_integral_upper_bound_from_MVP u R hR hu_harmonic hu_nonneg x hx d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hA_pos : 0 < R ^ 2 - CM8.euclidNorm x ^ 2 := by
    nlinarith [sq_nonneg (R - CM8.euclidNorm x)]


  have h1 : R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 =
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
  have h2 : (R ^ 2 - CM8.euclidNorm x ^ 2) * W ≤
      (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by linarith
  exact le_of_mul_le_mul_left h2 hA_pos

/-- Poisson estimate from a distance upper bound: produces the lower bound
$\frac{R^{n-2}(R^2 - |x|^2)}{d^n} u(0) \le u(x)$ when $\|x - \sigma\| \le d$. -/
theorem poisson_estimate_from_distance_upper {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → CM8.euclidNorm (x - σ) ≤ d) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 ≤ u x := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_lb := poisson_weight_lower_bound_axiom u R hR hu_harmonic hu_nonneg x hx W hW_eq d hd hd_bound


  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this
    exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]
  rw [hW_eq]


  calc R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0
      = (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by ring
    _ ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
        apply mul_le_mul_of_nonneg_left hW_lb hR2_sub

/-- Poisson estimate from a distance lower bound: produces the upper bound
$u(x) \le \frac{R^{n-2}(R^2 - |x|^2)}{d^n} u(0)$ when $d \le \|x - \sigma\|$. -/
theorem poisson_estimate_from_distance_lower {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R)
    (d : ℝ) (hd : 0 < d)
    (hd_bound : ∀ σ : Fin n → ℝ, CM8.euclidNorm σ = R → d ≤ CM8.euclidNorm (x - σ)) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by

  obtain ⟨W, hW_nn, hW_eq⟩ := poisson_representation_weight_axiom u R hR hu_harmonic hu_nonneg x hx

  have hW_ub := poisson_weight_upper_bound_axiom u R hR hu_harmonic hu_nonneg x hx W hW_eq d hd hd_bound

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this
    exact this
  have hx_nn : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  have hR2_sub : 0 ≤ R ^ 2 - CM8.euclidNorm x ^ 2 := by nlinarith [sq_nonneg (R - CM8.euclidNorm x), sq_nonneg (R + CM8.euclidNorm x)]

  rw [hW_eq]

  calc (R ^ 2 - CM8.euclidNorm x ^ 2) * W
      ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * (R ^ (n - 2) * u 0 / d ^ n) := by
        apply mul_le_mul_of_nonneg_left hW_ub hR2_sub
    _ = R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / d ^ n * u 0 := by ring

/-- Specialised lower Poisson estimate using $d = R + |x|$ (the maximum distance from $x$
to the sphere): $\frac{R^{n-2}(R^2 - |x|^2)}{(R + |x|)^n} u(0) \le u(x)$. -/
theorem poisson_integral_lower_estimate {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R) :
    R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / (R + CM8.euclidNorm x) ^ n * u 0 ≤ u x := by

  have hd : 0 < R + CM8.euclidNorm x := by
    have : 0 ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
    linarith

  exact poisson_estimate_from_distance_upper u R hR hu_harmonic hu_nonneg x hx
    (R + CM8.euclidNorm x) hd
    (fun σ hσ => distance_upper_bound_on_sphere x σ R hσ)

/-- Specialised upper Poisson estimate using $d = R - |x|$ (the minimum distance from $x$
to the sphere): $u(x) \le \frac{R^{n-2}(R^2 - |x|^2)}{(R - |x|)^n} u(0)$. -/
theorem poisson_integral_upper_estimate {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R) :
    u x ≤ R ^ (n - 2) * (R ^ 2 - CM8.euclidNorm x ^ 2) / (R - CM8.euclidNorm x) ^ n * u 0 := by

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this

  have hd : 0 < R - CM8.euclidNorm x := by linarith

  exact poisson_estimate_from_distance_lower u R hR hu_harmonic hu_nonneg x hx
    (R - CM8.euclidNorm x) hd
    (fun σ hσ => distance_lower_bound_on_sphere x σ R hσ)

/-- Algebraic simplification: $\frac{R^{n-2}(R^2 - d^2)}{(R+d)^n} = \frac{R^{n-2}(R - d)}{(R+d)^{n-1}}$,
using $R^2 - d^2 = (R - d)(R + d)$. -/
lemma lower_bound_simplify (R d a : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hRd : R + d ≠ 0) :
    R ^ (n - 2) * (R ^ 2 - d ^ 2) / (R + d) ^ n * a =
    R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1) * a := by
  have h1 : R ^ 2 - d ^ 2 = (R - d) * (R + d) := by ring
  rw [h1, show (R + d) ^ n = (R + d) ^ (n - 1) * (R + d) from by
    rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos (by omega)]]
  field_simp

/-- Algebraic simplification: $\frac{R^{n-2}(R^2 - d^2)}{(R-d)^n} = \frac{R^{n-2}(R + d)}{(R-d)^{n-1}}$. -/
lemma upper_bound_simplify (R d a : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hRd : R - d ≠ 0) :
    R ^ (n - 2) * (R ^ 2 - d ^ 2) / (R - d) ^ n * a =
    R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1) * a := by
  have h1 : R ^ 2 - d ^ 2 = (R + d) * (R - d) := by ring
  rw [h1, show (R - d) ^ n = (R - d) ^ (n - 1) * (R - d) from by
    rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos (by omega)]]
  field_simp
/-- The Euclidean norm on the trivial space $\mathbb{R}^0$ is identically zero. -/
lemma euclidNorm_fin_zero (x : Fin 0 → ℝ) : CM8.euclidNorm x = 0 := by
  unfold CM8.euclidNorm
  simp [Finset.sum_empty]

/-- Degenerate $n = 0$ case of the lower bound: simplifies away $|x|^2 = 0$. -/
lemma lower_bound_n_zero {u : (Fin 0 → ℝ) → ℝ} (R : ℝ) (hR : 0 < R)
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin 0 → ℝ) R, 0 ≤ u x)
    (x : Fin 0 → ℝ) (_hx : x ∈ euclidBall (0 : Fin 0 → ℝ) R)
    (h : (R ^ 2 - CM8.euclidNorm x ^ 2) * u 0 ≤ u x) :
    (R - CM8.euclidNorm x) * u 0 ≤ u x := by
  rw [euclidNorm_fin_zero x] at h ⊢
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero] at h ⊢

  have hx0 : x = 0 := by ext i; exact i.elim0
  rw [hx0] at h ⊢
  have hu0 : 0 ≤ u 0 := hu_nonneg 0 (by simp [euclidBall, CM8.euclidNorm]; exact hR)
  nlinarith [sq_nonneg (R - 1)]

/-- Degenerate $n = 0$ case of the upper bound: simplifies away $|x|^2 = 0$. -/
lemma upper_bound_n_zero {u : (Fin 0 → ℝ) → ℝ} (R : ℝ) (hR : 0 < R)
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin 0 → ℝ) R, 0 ≤ u x)
    (x : Fin 0 → ℝ) (_hx : x ∈ euclidBall (0 : Fin 0 → ℝ) R)
    (h : u x ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * u 0) :
    u x ≤ (R + CM8.euclidNorm x) * u 0 := by
  rw [euclidNorm_fin_zero x] at h ⊢
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero, add_zero] at h ⊢

  have hx0 : x = 0 := by ext i; exact i.elim0
  rw [hx0] at h ⊢
  have hu0 : 0 ≤ u 0 := hu_nonneg 0 (by simp [euclidBall, CM8.euclidNorm]; exact hR)
  nlinarith [sq_nonneg (R - 1)]

/-- The Euclidean norm is non-negative: $0 \le \|v\|$. -/
lemma euclidNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ CM8.euclidNorm v :=
  Real.sqrt_nonneg _

/-- Harnack-style lower bound (Poisson-kernel form):
$\frac{R^{n-2}(R - |x|)}{(R + |x|)^{n-1}} u(0) \le u(x)$
for $u$ harmonic and non-negative on $B_R(0)$. -/
theorem poisson_kernel_lower_bound {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R) :
    R ^ (n - 2) * (R - CM8.euclidNorm x) / (R + CM8.euclidNorm x) ^ (n - 1) * u 0 ≤ u x := by
  have h_ax := poisson_integral_lower_estimate u R hR hu_harmonic hu_nonneg x hx
  have hd := euclidNorm_nonneg x
  have hRd : R + CM8.euclidNorm x ≠ 0 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    simp only [pow_zero, one_mul, Nat.zero_sub, div_one] at h_ax ⊢
    exact lower_bound_n_zero R hR hu_nonneg x hx h_ax
  ·
    rw [← lower_bound_simplify R (CM8.euclidNorm x) (u 0) n (by omega) hRd]
    exact h_ax

/-- Harnack-style upper bound (Poisson-kernel form):
$u(x) \le \frac{R^{n-2}(R + |x|)}{(R - |x|)^{n-1}} u(0)$
for $u$ harmonic and non-negative on $B_R(0)$. -/
theorem poisson_kernel_upper_bound {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R) :
    u x ≤ R ^ (n - 2) * (R + CM8.euclidNorm x) / (R - CM8.euclidNorm x) ^ (n - 1) * u 0 := by
  have h_ax := poisson_integral_upper_estimate u R hR hu_harmonic hu_nonneg x hx
  have hd := euclidNorm_nonneg x

  have hx_lt : CM8.euclidNorm x < R := by
    have : CM8.euclidNorm (x - 0) < R := hx
    simp [sub_zero] at this; exact this
  have hRd : R - CM8.euclidNorm x ≠ 0 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    simp only [pow_zero, one_mul, Nat.zero_sub, div_one] at h_ax ⊢
    exact upper_bound_n_zero R hR hu_nonneg x hx h_ax
  ·
    rw [← upper_bound_simplify R (CM8.euclidNorm x) (u 0) n (by omega) hRd]
    exact h_ax

/-- **Theorem 4.1 (Harnack's inequality).** Let $u$ be harmonic and non-negative on the
ball $B_R(0) \subset \mathbb{R}^n$. Then for any $x \in B_R(0)$:
$\frac{R^{n-2}(R - |x|)}{(R + |x|)^{n-1}} u(0) \le u(x) \le \frac{R^{n-2}(R + |x|)}{(R - |x|)^{n-1}} u(0)$. -/
theorem harnack_inequality {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R)
    (hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
    (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
    (x : Fin n → ℝ) (hx : x ∈ euclidBall (0 : Fin n → ℝ) R) :
    R ^ (n - 2) * (R - CM8.euclidNorm x) / (R + CM8.euclidNorm x) ^ (n - 1) * u 0 ≤ u x ∧
    u x ≤ R ^ (n - 2) * (R + CM8.euclidNorm x) / (R - CM8.euclidNorm x) ^ (n - 1) * u 0 :=
  ⟨poisson_kernel_lower_bound u R hR hu_harmonic hu_nonneg x hx,
   poisson_kernel_upper_bound u R hR hu_harmonic hu_nonneg x hx⟩

/-- The Laplacian of a constant function vanishes identically: $\Delta(c) = 0$. -/
theorem laplacian_const {n : ℕ} (c : ℝ) :
    CM7.Laplacian n (fun _ : Fin n → ℝ => c) = fun _ => 0 :=
  CM7.laplacian_const c

/-- Every constant function is harmonic on any domain $\Omega \subset \mathbb{R}^n$. -/
lemma isHarmonic_const {n : ℕ} (c : ℝ) (Ω : Set (Fin n → ℝ)) :
    CM7.IsHarmonic (fun _ => c) Ω where
  contDiffOn := contDiff_const.contDiffOn
  laplacian_eq_zero := by
    intro x _
    have h := congr_fun (laplacian_const (n := n) c) x
    exact h

/-- Adding a constant preserves harmonicity: if $u$ is harmonic on $\Omega$, then so is $u + c$. -/
lemma IsHarmonic.add_const {n : ℕ} {u : (Fin n → ℝ) → ℝ} {Ω : Set (Fin n → ℝ)}
    (hu : CM7.IsHarmonic u Ω) (c : ℝ) (hΩ : IsOpen Ω) :
    CM7.IsHarmonic (fun x => u x + c) Ω := by

  have heq : (fun x => u x + c) = (fun x => u x - (fun _ => -c) x) := by
    ext x; ring
  rw [heq]
  exact hu.sub hΩ (isHarmonic_const (-c) Ω)

/-- A harmonic function on all of $\mathbb{R}^n$ is harmonic on any subset $\Omega$. -/
lemma IsHarmonic.restrict {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : CM7.IsHarmonic u Set.univ) (Ω : Set (Fin n → ℝ)) :
    CM7.IsHarmonic u Ω where
  contDiffOn := hu.contDiffOn.mono (Set.subset_univ _)
  laplacian_eq_zero := by
    intro x _
    exact hu.laplacian_eq_zero x (Set.mem_univ x)

/-- If $\|x\| < R$, then $x$ lies in the ball $B_R(0)$. -/
lemma mem_euclidBall_of_lt {n : ℕ} (x : Fin n → ℝ) (R : ℝ)
    (hR : CM8.euclidNorm x < R) :
    x ∈ euclidBall (0 : Fin n → ℝ) R := by
  show CM8.euclidNorm (x - 0) < R
  simp [sub_zero]
  exact hR

/-- Limit identity: $\frac{R}{R - d} \to 1$ as $R \to \infty$. -/
lemma tendsto_div_sub_const (d : ℝ) :
    Tendsto (fun R : ℝ => R / (R - d)) atTop (nhds 1) := by
  suffices h : Tendsto (fun R : ℝ => 1 + d / (R - d)) atTop (nhds (1 + 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop d] with R hR
    have hRd : R - d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_add
  apply Tendsto.div_atTop tendsto_const_nhds
  exact (tendsto_atTop_add_const_right atTop (-d) tendsto_id)

/-- Limit identity: $\left(\frac{R}{R - d}\right)^k \to 1$ as $R \to \infty$. -/
lemma tendsto_pow_ratio (k : ℕ) (d : ℝ) :
    Tendsto (fun R : ℝ => R ^ k / (R - d) ^ k) atTop (nhds 1) := by
  rw [show (fun R : ℝ => R ^ k / (R - d) ^ k) = (fun R => (R / (R - d)) ^ k) from
    by ext R; rw [div_pow], show (1 : ℝ) = 1 ^ k from (one_pow k).symm]
  exact (tendsto_div_sub_const d).pow k

/-- Limit identity: $\frac{R + d}{R - d} \to 1$ as $R \to \infty$. -/
lemma tendsto_add_div_sub (d : ℝ) :
    Tendsto (fun R : ℝ => (R + d) / (R - d)) atTop (nhds 1) := by
  suffices h : Tendsto (fun R : ℝ => 1 + 2 * d / (R - d)) atTop (nhds (1 + 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop d] with R hR
    have hRd : R - d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_add
  apply Tendsto.div_atTop tendsto_const_nhds
  exact (tendsto_atTop_add_const_right atTop (-d) tendsto_id)

/-- Limit identity: $\frac{R - d}{R + d} \to 1$ as $R \to \infty$, for $d \ge 0$. -/
lemma tendsto_sub_div_add (d : ℝ) (hd : 0 ≤ d) :
    Tendsto (fun R : ℝ => (R - d) / (R + d)) atTop (nhds 1) := by
  suffices h : Tendsto (fun R : ℝ => 1 - 2 * d / (R + d)) atTop (nhds (1 - 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have hRd : R + d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_sub
  apply Tendsto.div_atTop tendsto_const_nhds
  exact tendsto_atTop_add_const_right atTop d tendsto_id

/-- Limit identity: $\frac{R}{R + d} \to 1$ as $R \to \infty$, for $d \ge 0$. -/
lemma tendsto_div_add_const (d : ℝ) (hd : 0 ≤ d) :
    Tendsto (fun R : ℝ => R / (R + d)) atTop (nhds 1) := by
  suffices h : Tendsto (fun R : ℝ => 1 - d / (R + d)) atTop (nhds (1 - 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have hRd : R + d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_sub
  apply Tendsto.div_atTop tendsto_const_nhds
  exact tendsto_atTop_add_const_right atTop d tendsto_id

/-- Limit identity: $\left(\frac{R}{R + d}\right)^k \to 1$ as $R \to \infty$, for $d \ge 0$. -/
lemma tendsto_pow_ratio_add (k : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    Tendsto (fun R : ℝ => R ^ k / (R + d) ^ k) atTop (nhds 1) := by
  rw [show (fun R : ℝ => R ^ k / (R + d) ^ k) = (fun R => (R / (R + d)) ^ k) from
    by ext R; rw [div_pow], show (1 : ℝ) = 1 ^ k from (one_pow k).symm]
  exact (tendsto_div_add_const d hd).pow k

/-- Limit of the upper Harnack coefficient: $\frac{R^{n-2}(R+d)}{(R-d)^{n-1}} \to 1$ as $R \to \infty$. -/
lemma tendsto_upper_coeff (n : ℕ) (hn : 2 ≤ n) (d : ℝ) :
    Tendsto (fun R : ℝ => R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1)) atTop (nhds 1) := by
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  rw [show (1 : ℝ) = 1 * 1 from (mul_one 1).symm]
  refine Tendsto.congr ?_ ((tendsto_pow_ratio (n - 2) d).mul (tendsto_add_div_sub d))
  intro R
  simp only [hn1, pow_succ]
  by_cases hRd : R - d = 0
  · simp [hRd]
  · field_simp

/-- Limit of the lower Harnack coefficient: $\frac{R^{n-2}(R-d)}{(R+d)^{n-1}} \to 1$ as $R \to \infty$. -/
lemma tendsto_lower_coeff (n : ℕ) (hn : 2 ≤ n) (d : ℝ) (hd : 0 ≤ d) :
    Tendsto (fun R : ℝ => R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1)) atTop (nhds 1) := by
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  rw [show (1 : ℝ) = 1 * 1 from (mul_one 1).symm]
  refine Tendsto.congr ?_ ((tendsto_pow_ratio_add (n - 2) d hd).mul (tendsto_sub_div_add d hd))
  intro R
  simp only [hn1, pow_succ]
  by_cases hRd : R + d = 0
  · simp [hRd]
  · field_simp

/-- Harnack squeeze principle: if $b$ is squeezed between the lower and upper Harnack
coefficients applied to $a$ for all sufficiently large $R$, then taking $R \to \infty$
forces $b = a$. This is the key analytical step in deducing Liouville's theorem from
Harnack's inequality. -/
theorem harnack_upper_squeeze {n : ℕ} (d : ℝ) (hd : 0 ≤ d) (a b : ℝ)
    (h_le : ∀ R : ℝ, d < R →
      b ≤ R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1) * a)
    (h_ge : ∀ R : ℝ, d < R →
      R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1) * a ≤ b) :
    b = a := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  ·
    have hn2 : n - 2 = 0 := by omega
    have hn1 : n - 1 = 0 := by omega
    simp only [hn2, hn1, pow_zero, one_mul, div_one] at h_le h_ge


    have ha : a = 0 := by
      by_contra ha_ne
      rcases lt_or_gt_of_ne ha_ne with ha_neg | ha_pos
      ·
        have hna : (0 : ℝ) < -a := neg_pos.mpr ha_neg
        have hab : (0 : ℝ) < (|b| + 1) / (-a) := div_pos (by positivity) hna
        have hR : d < d + (|b| + 1) / (-a) + 1 := by linarith
        have h := h_le (d + (|b| + 1) / (-a) + 1) hR
        have hineq : (d + (|b| + 1) / (-a) + 1 + d) * a ≤ ((|b| + 1) / (-a) + 1) * a := by
          nlinarith [mul_le_mul_of_nonpos_right
            (show d + (|b| + 1) / (-a) + 1 + d ≥ (|b| + 1) / (-a) + 1 from by linarith)
            (le_of_lt ha_neg)]
        have hval : ((|b| + 1) / (-a) + 1) * a = -(|b| + 1) + a := by
          field_simp
        linarith [neg_abs_le b]
      ·
        have hab : (0 : ℝ) < (|b| + 1) / a := div_pos (by positivity) ha_pos
        have hR : d < d + (|b| + 1) / a + 1 := by linarith
        have h := h_ge (d + (|b| + 1) / a + 1) hR
        have hsimp : (d + (|b| + 1) / a + 1 - d) * a = |b| + 1 + a := by
          field_simp; ring
        linarith [le_abs_self b]
    subst ha
    have h1 := h_ge (d + 1) (by linarith)
    have h2 := h_le (d + 1) (by linarith)
    linarith
  ·
    apply le_antisymm
    ·
      have hlim : Tendsto (fun R => R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1) * a)
          atTop (nhds (1 * a)) :=
        (tendsto_upper_coeff n hn d).mul tendsto_const_nhds
      simp only [one_mul] at hlim
      exact ge_of_tendsto hlim
        (eventually_atTop.mpr ⟨d + 1, fun R hR => h_le R (by linarith)⟩)
    ·
      have hlim : Tendsto (fun R => R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1) * a)
          atTop (nhds (1 * a)) :=
        (tendsto_lower_coeff n hn d hd).mul tendsto_const_nhds
      simp only [one_mul] at hlim
      exact le_of_tendsto hlim
        (eventually_atTop.mpr ⟨d + 1, fun R hR => h_ge R (by linarith)⟩)

/-- Liouville's theorem for non-negative harmonic functions: a non-negative harmonic function
on $\mathbb{R}^n$ is constant. -/
lemma liouville_nonneg {n : ℕ} (v : (Fin n → ℝ) → ℝ)
    (hv_harmonic : CM7.IsHarmonic v Set.univ)
    (hv_nonneg : ∀ x, 0 ≤ v x) :
    ∃ c : ℝ, ∀ x, v x = c := by
  use v 0
  intro x
  have hd_nn : (0 : ℝ) ≤ CM8.euclidNorm x := Real.sqrt_nonneg _
  apply harnack_upper_squeeze (n := n) (CM8.euclidNorm x) hd_nn (v 0) (v x)
  · intro R hR
    have hR_pos : (0 : ℝ) < R := lt_of_le_of_lt hd_nn hR
    have hx_mem : x ∈ euclidBall (0 : Fin n → ℝ) R := mem_euclidBall_of_lt x R hR
    have hv_ball : CM7.IsHarmonic v (euclidBall 0 R) := IsHarmonic.restrict hv_harmonic _
    have hv_nn_ball : ∀ y ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ v y :=
      fun y _ => hv_nonneg y
    exact (harnack_inequality v R hR_pos hv_ball hv_nn_ball x hx_mem).2
  · intro R hR
    have hR_pos : (0 : ℝ) < R := lt_of_le_of_lt hd_nn hR
    have hx_mem : x ∈ euclidBall (0 : Fin n → ℝ) R := mem_euclidBall_of_lt x R hR
    have hv_ball : CM7.IsHarmonic v (euclidBall 0 R) := IsHarmonic.restrict hv_harmonic _
    have hv_nn_ball : ∀ y ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ v y :=
      fun y _ => hv_nonneg y
    exact (harnack_inequality v R hR_pos hv_ball hv_nn_ball x hx_mem).1

/-- **Corollary 4.0.4 (Liouville's theorem).** Suppose $u \in C^2(\mathbb{R}^n)$ is harmonic
on all of $\mathbb{R}^n$, and there exists $M \in \mathbb{R}$ such that either $u(x) \ge M$
for all $x$ or $u(x) \le M$ for all $x$. Then $u$ is constant. -/
theorem liouville_theorem {n : ℕ}
    (u : (Fin n → ℝ) → ℝ)
    (hu_harmonic : CM7.IsHarmonic u Set.univ)
    (_hu_smooth : ContDiff ℝ 2 u)
    (M : ℝ) (hu_bdd : (∀ x, M ≤ u x) ∨ (∀ x, u x ≤ M)) :
    ∃ c : ℝ, ∀ x, u x = c := by
  rcases hu_bdd with hbelow | habove
  ·

    have hv_harmonic : CM7.IsHarmonic (fun x => u x + |M|) Set.univ :=
      IsHarmonic.add_const hu_harmonic |M| isOpen_univ
    have hv_nonneg : ∀ x, 0 ≤ (fun x => u x + |M|) x := by
      intro x; simp
      have h1 := hbelow x
      have h2 := add_abs_nonneg M
      linarith
    obtain ⟨c, hc⟩ := liouville_nonneg (fun x => u x + |M|) hv_harmonic hv_nonneg
    exact ⟨c - |M|, fun x => by have := hc x; linarith⟩
  ·

    have hw_harmonic : CM7.IsHarmonic (fun x => -u x + |M|) Set.univ :=
      IsHarmonic.add_const (CM7.IsHarmonic.neg hu_harmonic) |M| isOpen_univ
    have hw_nonneg : ∀ x, 0 ≤ (fun x => -u x + |M|) x := by
      intro x; simp
      have h1 := habove x
      have h2 := le_abs_self M
      linarith
    obtain ⟨c, hc⟩ := liouville_nonneg (fun x => -u x + |M|) hw_harmonic hw_nonneg
    exact ⟨-(c - |M|), fun x => by have := hc x; linarith⟩

end PoissonHarnack
