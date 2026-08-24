/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.FourierMultiplier
open MeasureTheory Complex FourierTransform

noncomputable section

namespace SchrodingerEquation

/-- Abbreviation for the $n$-dimensional Euclidean space $\mathbb{R}^n$. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The predicate that $\psi : \mathbb{R} \times \mathbb{R} \to \mathbb{C}$ solves the 1D free
Schrödinger equation $i\partial_t \psi + \tfrac{1}{2}\partial_x^2 \psi = 0$ on $t > 0$. -/
def IsFreeSchrodingerSolution (ψ : ℝ → ℝ → ℂ) : Prop :=
  ∀ t > (0 : ℝ), ∀ x : ℝ,
    I * deriv (fun s => ψ s x) t +
    (1 / 2 : ℂ) * deriv (deriv (ψ t)) x = 0

/-- The complex Laplacian $\Delta f(x) = \sum_{j=1}^n \partial_{x_j}^2 f(x)$ for a complex-valued
function $f : \mathbb{R}^n \to \mathbb{C}$, defined via iterated Fréchet derivatives along the
standard basis directions. -/
def complexLaplacian {n : ℕ} (f : Rn n → ℂ) (x : Rn n) : ℂ :=
  ∑ j : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)

/-- The predicate that $\psi : \mathbb{R} \times \mathbb{R}^n \to \mathbb{C}$ solves the
$n$-dimensional free Schrödinger equation $i\partial_t \psi + \tfrac{1}{2}\Delta \psi = 0$
on $t > 0$. -/
def IsFreeSchrodingerSolutionND {n : ℕ} (ψ : ℝ → Rn n → ℂ) : Prop :=
  ∀ t > (0 : ℝ), ∀ x : Rn n,
    I * deriv (fun s => ψ s x) t +
    (1 / 2 : ℂ) * complexLaplacian (ψ t) x = 0

/-- The Fourier transform of the 1D Schrödinger fundamental solution:
$\hat{K}(t, \xi) = e^{-2\pi^2 i t \xi^2}$. -/
def fundamentalSolutionFT (t ξ : ℝ) : ℂ :=
  exp (((-2 * Real.pi ^ 2 * t * ξ ^ 2 : ℝ) : ℂ) * I)

/-- The Fourier transform of the 1D free Schrödinger solution with initial data $\phi$:
$\hat{\psi}(t,\xi) = \hat{K}(t,\xi)\hat{\phi}(\xi)$. -/
def solutionFT (φ : ℝ → ℂ) (t ξ : ℝ) : ℂ :=
  fundamentalSolutionFT t ξ * CM16.fourierTransform φ ξ

/-- **Definition 2.0.1.** The fundamental solution to the free Schrödinger equation in
$\mathbb{R}^n$:
$$K(t, x) = \frac{1}{(2\pi i t)^{n/2}} e^{i |x|^2 / (2t)}.$$ -/
def schrodingerKernel {n : ℕ} (t : ℝ) (x : Rn n) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(↑n : ℂ) / 2) *
  exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ))

/-- The 1D specialization of the Schrödinger fundamental solution:
$K(t, x) = (2\pi i t)^{-1/2} e^{i x^2 / (2t)}$ for $x \in \mathbb{R}$. -/
def schrodingerKernel1D (t x : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(1 : ℂ) / 2) *
  exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ))

/-- The pointwise modulus of the Schrödinger kernel in dimension $n$ is
$|K(t,x)| = (2\pi t)^{-n/2}$ for $t > 0$, independently of $x$. -/
theorem schrodingerKernel_norm {n : ℕ} (t : ℝ) (x : Rn n) (ht : t > 0) :
    ‖schrodingerKernel t x‖ = (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) := by
  unfold schrodingerKernel
  rw [norm_mul]

  have hexp : ‖exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, mul_one]

  have hcast : (-(↑n : ℂ) / 2) = (↑(-(↑n : ℝ) / 2) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_real]
  have hnorm : ‖((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)‖ = 2 * Real.pi * t := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_real, Complex.norm_I, mul_one]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    rw [Real.norm_of_nonneg (le_of_lt ht)]
  rw [hnorm]

/-- In 1D, $|K(t,x)| = 1 / \sqrt{2\pi t}$ for $t > 0$. -/
theorem schrodingerKernel1D_norm (t : ℝ) (x : ℝ) (ht : t > 0) :
    ‖schrodingerKernel1D t x‖ = 1 / Real.sqrt (2 * Real.pi * t) := by
  unfold schrodingerKernel1D
  rw [norm_mul]
  have hexp : ‖exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, mul_one]
  have hcast : (-(1 : ℂ) / 2) = (↑((-1 : ℝ) / 2) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_real]
  have hnorm : ‖((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)‖ = 2 * Real.pi * t := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_real, Complex.norm_I, mul_one]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    rw [Real.norm_of_nonneg (le_of_lt ht)]
  rw [hnorm]
  have hpos : 0 < 2 * Real.pi * t := by positivity
  rw [show (-1 : ℝ) / 2 = -(1/2 : ℝ) from by ring]
  rw [Real.rpow_neg (le_of_lt hpos)]
  rw [← Real.sqrt_eq_rpow]
  rw [one_div]

/-- The convolution $(K(t, \cdot) * \phi)(x) = \int_{\mathbb{R}} K(t, x - y) \phi(y) \, dy$
in 1D, giving the candidate solution to the free Schrödinger equation with initial data $\phi$. -/
def schrodingerConvolution (φ : ℝ → ℂ) (t x : ℝ) : ℂ :=
  ∫ y : ℝ, schrodingerKernel1D t (x - y) * φ y

/-- Computation of the time derivative of the 1D Schrödinger kernel:
$i\partial_t K(t,x) = K(t,x) \cdot \left(-\frac{i}{2t} + \frac{x^2}{2t^2}\right)$. -/
theorem schrodingerKernel1D_time_deriv (t x : ℝ) (ht : t > 0) :
    I * deriv (fun s => schrodingerKernel1D s x) t =
    schrodingerKernel1D t x * (-I / (2 * ↑t) + (↑(x ^ 2) : ℂ) / (2 * ↑t ^ 2)) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have htne_c : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_ne
  set c2pi := (↑(2 * Real.pi) : ℂ) with hc2pi_def
  have hc2pi_ne : c2pi ≠ 0 := by simp only [c2pi, ofReal_ne_zero]; positivity
  have hbase_ne : c2pi * I * ↑t ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc2pi_ne I_ne_zero) htne_c
  have hbase_mem : c2pi * I * ↑t ∈ Complex.slitPlane := by
    have heq : c2pi * I * ↑t = ↑(2 * Real.pi * t) * I := by simp [c2pi]; ring
    rw [heq, Complex.mem_slitPlane_iff]; right
    simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]; positivity
  have hderiv_cpow : HasDerivAt (fun s : ℝ => (c2pi * I * ↑s) ^ ((-1 : ℂ) / 2))
      ((-1 : ℂ) / 2 * (c2pi * I * ↑t) ^ ((-1 : ℂ) / 2 - 1) * (c2pi * I)) t := by
    have hlin : HasDerivAt (fun z : ℂ => c2pi * I * z) (c2pi * I) (↑t : ℂ) := by
      have h2 := (hasDerivAt_id (↑t : ℂ)).const_mul (c2pi * I)
      simp [mul_one] at h2; exact h2
    exact (hlin.cpow_const hbase_mem).comp_ofReal
  have hderiv_exp : HasDerivAt (fun s : ℝ => exp (I * ((x ^ 2 / (2 * s) : ℝ) : ℂ)))
      (exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ)) * (I * ((-x ^ 2 / (2 * t ^ 2) : ℝ) : ℂ))) t := by
    have hq : HasDerivAt (fun s : ℝ => (x ^ 2 / (2 * s) : ℝ)) (-x ^ 2 / (2 * t ^ 2)) t := by
      have := (hasDerivAt_inv ht_ne).const_mul (x ^ 2 / 2)
      simp only [mul_neg] at this
      convert this using 1 <;> [ext s; skip] <;> ring
    exact (hq.ofReal_comp.const_mul I).cexp
  have hK : HasDerivAt (fun s => schrodingerKernel1D s x)
      (((-1 : ℂ) / 2 * (c2pi * I * ↑t) ^ ((-1 : ℂ) / 2 - 1) * (c2pi * I)) *
        exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ)) +
      (c2pi * I * ↑t) ^ ((-1 : ℂ) / 2) *
        (exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ)) * (I * ((-x ^ 2 / (2 * t ^ 2) : ℝ) : ℂ)))) t := by
    have hprod := hderiv_cpow.mul hderiv_exp
    have : (fun s => (c2pi * I * ↑s) ^ ((-1 : ℂ) / 2) *
        exp (I * ((x ^ 2 / (2 * s) : ℝ) : ℂ))) = (fun s => schrodingerKernel1D s x) := by
      funext s; simp only [schrodingerKernel1D]; ring
    rwa [← this]
  rw [hK.deriv]
  set z := c2pi * I * (↑t : ℂ)
  set e := exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ))
  have hcpow_sub : z ^ ((-1 : ℂ) / 2 - 1) = z ^ ((-1 : ℂ) / 2) / z := by
    have h := Complex.cpow_sub ((-1 : ℂ) / 2) 1 hbase_ne
    rw [cpow_one] at h; exact h
  rw [hcpow_sub]
  have hz_div : c2pi * I / z = 1 / ↑t := by simp only [z]; field_simp
  rw [show (-1 : ℂ) / 2 * (z ^ ((-1 : ℂ) / 2) / z) * (c2pi * I) =
      z ^ ((-1 : ℂ) / 2) * ((-1 : ℂ) / 2 * (c2pi * I / z)) from by ring]
  rw [hz_div]
  have hKval : schrodingerKernel1D t x = z ^ ((-1 : ℂ) / 2) * e := by
    simp only [schrodingerKernel1D, z, e]; ring
  rw [hKval]
  ring_nf
  rw [I_sq]
  push_cast
  ring_nf

/-- Computation of the spatial Laplacian of the 1D Schrödinger kernel:
$\tfrac{1}{2}\partial_x^2 K(t,x) = K(t,x) \cdot \left(\frac{i}{2t} - \frac{x^2}{2t^2}\right)$. -/
theorem schrodingerKernel1D_laplacian (t x : ℝ) (ht : t > 0) :
    (1 / 2 : ℂ) * deriv (deriv (schrodingerKernel1D t)) x =
    schrodingerKernel1D t x * (I / (2 * ↑t) - (↑(x ^ 2) : ℂ) / (2 * ↑t ^ 2)) := by


  have hK_deriv : ∀ y : ℝ, HasDerivAt (schrodingerKernel1D t)
      (schrodingerKernel1D t y * (I * ↑y / ↑t)) y := by
    intro y
    unfold schrodingerKernel1D
    set C := (((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(1 : ℂ) / 2)
    have hg : HasDerivAt (fun z : ℝ => (z ^ 2 / (2 * t) : ℝ)) (y / t) y := by
      have h : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        have := hasDerivAt_pow 2 y; simp at this; exact this
      convert h.div_const (2 * t) using 1; field_simp
    have hIg : HasDerivAt (fun z : ℝ => I * ((z ^ 2 / (2 * t) : ℝ) : ℂ)) (I * ↑(y / t)) y :=
      (HasDerivAt.ofReal_comp hg).const_mul I
    have hexp := HasDerivAt.cexp hIg
    have hfull := hexp.const_mul C
    convert hfull using 1
    push_cast; ring

  have h_deriv_eq : deriv (schrodingerKernel1D t) =
      fun y => schrodingerKernel1D t y * (I * ↑y / ↑t) := by
    ext y; exact (hK_deriv y).deriv

  rw [h_deriv_eq]

  have hg : HasDerivAt (fun y : ℝ => I * (↑y : ℂ) / (↑t : ℂ)) (I / ↑t) x := by
    have h : HasDerivAt (⇑ofRealCLM) (ofRealCLM 1) x := ContinuousLinearMap.hasDerivAt ofRealCLM
    simp [ofRealCLM_apply, ofReal_one] at h
    have h2 := (h.const_mul I).div_const (↑t : ℂ)
    convert h2 using 1; ring

  have h_prod : HasDerivAt (fun y => schrodingerKernel1D t y * (I * ↑y / ↑t))
      (schrodingerKernel1D t x * (I * ↑x / ↑t) * (I * ↑x / ↑t) +
       schrodingerKernel1D t x * (I / ↑t)) x :=
    (hK_deriv x).mul hg
  rw [h_prod.deriv]

  have ht' : (↑t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have key : schrodingerKernel1D t x * (I * ↑x / ↑t) * (I * ↑x / ↑t) =
      schrodingerKernel1D t x * (I ^ 2 * (↑x) ^ 2 / (↑t) ^ 2) := by ring
  rw [key, I_sq]
  push_cast
  field_simp
  ring

/-- **Lemma 2.0.2 (1D case).** The fundamental solution $K(t,x)$ verifies the free Schrödinger
equation $i\partial_t K + \tfrac{1}{2}\partial_x^2 K = 0$ for $t > 0$. -/
theorem lemma_2_0_2_K_solves_schrodinger :
    IsFreeSchrodingerSolution (fun t x => schrodingerKernel1D t x) := by
  intro t ht x
  rw [schrodingerKernel1D_time_deriv t x ht, schrodingerKernel1D_laplacian t x ht]
  ring

/-- The time derivative of the $n$-dimensional Schrödinger kernel:
$i\partial_t K(t,x) = K(t,x) \cdot \left(-\frac{n i}{2t} + \frac{|x|^2}{2t^2}\right)$. -/
theorem schrodingerKernel_time_deriv {n : ℕ} (t : ℝ) (x : Rn n) (ht : t > 0) :
    I * deriv (fun s => schrodingerKernel (n := n) s x) t =
    schrodingerKernel t x *
      (-(↑n : ℂ) * I / (2 * ↑t) + (↑(‖x‖ ^ 2) : ℂ) / (2 * ↑t ^ 2)) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have htne_c : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_ne
  set c2pi := (↑(2 * Real.pi) : ℂ) with hc2pi_def
  have hc2pi_ne : c2pi ≠ 0 := by simp only [c2pi, ofReal_ne_zero]; positivity
  have hbase_ne : c2pi * I * ↑t ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc2pi_ne I_ne_zero) htne_c
  have hbase_mem : c2pi * I * ↑t ∈ Complex.slitPlane := by
    have heq : c2pi * I * ↑t = ↑(2 * Real.pi * t) * I := by simp [c2pi]; ring
    rw [heq, Complex.mem_slitPlane_iff]; right
    simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]; positivity

  have hderiv_cpow : HasDerivAt (fun s : ℝ => (c2pi * I * ↑s) ^ (-(↑n : ℂ) / 2))
      (-(↑n : ℂ) / 2 * (c2pi * I * ↑t) ^ (-(↑n : ℂ) / 2 - 1) * (c2pi * I)) t := by
    have hlin : HasDerivAt (fun z : ℂ => c2pi * I * z) (c2pi * I) (↑t : ℂ) := by
      have h2 := (hasDerivAt_id (↑t : ℂ)).const_mul (c2pi * I)
      simp [mul_one] at h2; exact h2
    exact (hlin.cpow_const hbase_mem).comp_ofReal

  have hderiv_exp : HasDerivAt (fun s : ℝ => exp (I * ((‖x‖ ^ 2 / (2 * s) : ℝ) : ℂ)))
      (exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ)) *
        (I * ((-‖x‖ ^ 2 / (2 * t ^ 2) : ℝ) : ℂ))) t := by
    have hq : HasDerivAt (fun s : ℝ => (‖x‖ ^ 2 / (2 * s) : ℝ))
        (-‖x‖ ^ 2 / (2 * t ^ 2)) t := by
      have := (hasDerivAt_inv ht_ne).const_mul (‖x‖ ^ 2 / 2)
      simp only [mul_neg] at this
      convert this using 1 <;> [ext s; skip] <;> ring
    exact (hq.ofReal_comp.const_mul I).cexp

  have hK : HasDerivAt (fun s => schrodingerKernel (n := n) s x)
      ((-(↑n : ℂ) / 2 * (c2pi * I * ↑t) ^ (-(↑n : ℂ) / 2 - 1) * (c2pi * I)) *
        exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ)) +
      (c2pi * I * ↑t) ^ (-(↑n : ℂ) / 2) *
        (exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ)) *
          (I * ((-‖x‖ ^ 2 / (2 * t ^ 2) : ℝ) : ℂ)))) t := by
    have hprod := hderiv_cpow.mul hderiv_exp
    have : (fun s => (c2pi * I * ↑s) ^ (-(↑n : ℂ) / 2) *
        exp (I * ((‖x‖ ^ 2 / (2 * s) : ℝ) : ℂ))) =
        (fun s => schrodingerKernel (n := n) s x) := by
      funext s; simp only [schrodingerKernel]; ring
    rwa [← this]
  rw [hK.deriv]
  set z := c2pi * I * (↑t : ℂ)
  set e := exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ))

  have hcpow_sub : z ^ (-(↑n : ℂ) / 2 - 1) = z ^ (-(↑n : ℂ) / 2) / z := by
    have h := Complex.cpow_sub (-(↑n : ℂ) / 2) 1 hbase_ne
    rw [cpow_one] at h; exact h
  rw [hcpow_sub]
  have hz_div : c2pi * I / z = 1 / ↑t := by simp only [z]; field_simp
  rw [show -(↑n : ℂ) / 2 * (z ^ (-(↑n : ℂ) / 2) / z) * (c2pi * I) =
      z ^ (-(↑n : ℂ) / 2) * (-(↑n : ℂ) / 2 * (c2pi * I / z)) from by ring]
  rw [hz_div]
  have hKval : schrodingerKernel t x = z ^ (-(↑n : ℂ) / 2) * e := by
    simp only [schrodingerKernel, z, e]; ring
  rw [hKval]
  ring_nf
  rw [I_sq]
  push_cast
  ring_nf

/-- The second partial derivative of the $n$-dimensional Schrödinger kernel in the $j$-th direction:
$\partial_{x_j}^2 K(t,x) = K(t,x) \cdot \left(\frac{i}{t} + \left(\frac{i x_j}{t}\right)^2\right)$. -/
theorem schrodingerKernel_second_partial {n : ℕ} (t : ℝ) (x : Rn n) (ht : t > 0)
    (j : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ (schrodingerKernel (n := n) t) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1) =
    schrodingerKernel t x * (I / ↑t + (I * ↑(x j) / ↑t) ^ 2) := by sorry

/-- Computation of the spatial Laplacian of the $n$-dimensional Schrödinger kernel:
$\tfrac{1}{2}\Delta K(t,x) = K(t,x) \cdot \left(\frac{n i}{2t} - \frac{|x|^2}{2t^2}\right)$. -/
theorem schrodingerKernel_laplacian {n : ℕ} (t : ℝ) (x : Rn n) (ht : t > 0) :
    (1 / 2 : ℂ) * complexLaplacian (schrodingerKernel (n := n) t) x =
    schrodingerKernel t x *
      ((↑n : ℂ) * I / (2 * ↑t) - (↑(‖x‖ ^ 2) : ℂ) / (2 * ↑t ^ 2)) := by

  have hpartial2 : ∀ j : Fin n,
      fderiv ℝ (fun y => fderiv ℝ (schrodingerKernel (n := n) t) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1) =
      schrodingerKernel t x * (I / ↑t + (I * ↑(x j) / ↑t) ^ 2) :=
    fun j => schrodingerKernel_second_partial t x ht j


  unfold complexLaplacian
  simp_rw [hpartial2]
  rw [← Finset.mul_sum]

  have hsum : ∑ j : Fin n, (I / (↑t : ℂ) + (I * ↑(x j) / ↑t) ^ 2) =
      ↑n * I / ↑t + I ^ 2 * ↑(‖x‖ ^ 2) / (↑t) ^ 2 := by
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.sum_const, Finset.card_fin, Nat.smul_one_eq_cast]
      ring
    · simp_rw [div_pow, mul_pow]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      congr 1
      rw [EuclideanSpace.real_norm_sq_eq]
      push_cast
      rfl
  rw [hsum, I_sq]
  push_cast
  ring

/-- **Lemma 2.0.2 ($n$-dimensional case).** The fundamental solution $K(t,x)$ verifies the free
Schrödinger equation $i\partial_t K + \tfrac{1}{2}\Delta K = 0$ for $t > 0$, $x \in \mathbb{R}^n$. -/
theorem lemma_2_0_2_K_solves_schrodinger_nD {n : ℕ} :
    IsFreeSchrodingerSolutionND (fun t x => schrodingerKernel (n := n) t x) := by
  intro t ht x
  rw [schrodingerKernel_time_deriv t x ht, schrodingerKernel_laplacian t x ht]
  ring

/-- **Proposition 2.0.3 (1D case).** For $\phi \in C_c^\infty(\mathbb{R})$, the convolution
$(K(t,\cdot) * \phi)(x)$ recovers the initial data as $t \to 0^+$:
$\lim_{t \to 0^+} (K(t,\cdot) * \phi)(x) = \phi(x)$. -/
theorem proposition_2_0_3_initial_data_recovery
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (x : ℝ) :
    Filter.Tendsto (fun t => schrodingerConvolution φ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)) := by sorry

/-- The candidate 1D solution $\psi(t, x) = (K(t, \cdot) * \phi)(x)$ to the free Schrödinger
equation with initial data $\phi$. -/
def schrodingerSolution (φ : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun t x => schrodingerConvolution φ t x

/-- The convolution $(K(t,\cdot) * \phi)(x) = \int_{\mathbb{R}^n} K(t, x - y) \phi(y) \, d^n y$
in $n$ dimensions. -/
def schrodingerConvolutionND {n : ℕ} (φ : Rn n → ℂ) (t : ℝ) (x : Rn n) : ℂ :=
  ∫ y : Rn n, schrodingerKernel t (x - y) * φ y

/-- The candidate $n$-dimensional solution $\psi(t, x) = (K(t, \cdot) * \phi)(x)$ to the free
Schrödinger equation with initial data $\phi : \mathbb{R}^n \to \mathbb{C}$. -/
def schrodingerSolutionND {n : ℕ} (φ : Rn n → ℂ) : ℝ → Rn n → ℂ :=
  fun t x => schrodingerConvolutionND φ t x

/-- **Proposition 2.0.3 ($n$-dimensional case).** For $\phi \in C_c^\infty(\mathbb{R}^n)$,
$\lim_{t \to 0^+} \frac{1}{(2\pi i t)^{n/2}} \int_{\mathbb{R}^n} e^{i |x-y|^2 / (2t)} \phi(y)\, d^n y = \phi(x)$. -/
theorem proposition_2_0_3_initial_data_recovery_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (x : Rn n) :
    Filter.Tendsto (fun t => schrodingerConvolutionND φ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)) := by sorry

/-- The differentiation-under-the-integral identity: the 1D convolution
$K(t,\cdot) * \phi$ solves the free Schrödinger equation, obtained by passing the time and
spatial derivatives inside the integral. -/
theorem differentiation_under_integral_schrodinger
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    I * deriv (fun s => schrodingerConvolution φ s x) t +
    (1 / 2 : ℂ) * deriv (deriv (schrodingerConvolution φ t)) x = 0 := by sorry

/-- For $\phi \in C_c^\infty(\mathbb{R})$, the 1D Schrödinger convolution
$(t, x) \mapsto (K(t, \cdot) * \phi)(x)$ is $C^\infty$ jointly in $(t, x)$. -/
theorem smoothness_schrodinger_convolution
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => schrodingerConvolution φ p.1 p.2) := by sorry

/-- **Theorem 2.1 (existence, 1D).** The candidate solution $\psi = K(t, \cdot) * \phi$ indeed
solves the free Schrödinger equation for $t > 0$. -/
theorem theorem_2_1_solves_equation
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
    IsFreeSchrodingerSolution (schrodingerSolution φ) := by
  intro t ht x
  exact differentiation_under_integral_schrodinger φ hφ_smooth hφ_supp t ht x

/-- **Theorem 2.1 (initial data, 1D).** The candidate solution $\psi$ attains the initial data
$\phi$ as $t \to 0^+$. -/
theorem theorem_2_1_initial_data
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (x : ℝ) :
    Filter.Tendsto (fun t => schrodingerSolution φ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)) :=
  proposition_2_0_3_initial_data_recovery φ hφ_smooth hφ_supp x

/-- **Theorem 2.1 (smoothness, 1D).** The solution $\psi(t, x)$ is smooth in $(t, x)$. -/
theorem theorem_2_1_smoothness
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => schrodingerSolution φ p.1 p.2) :=
  smoothness_schrodinger_convolution φ hφ_smooth hφ_supp

/-- **Theorem 2.1 (dispersive estimate, 1D).** For $t > 0$, the solution satisfies
$\|\psi(t, \cdot)\|_{L^\infty} \le \frac{1}{\sqrt{2\pi t}} \|\phi\|_{L^1}$. -/
theorem theorem_2_1_dispersive_estimate
    (φ : ℝ → ℂ) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ‖schrodingerSolution φ t x‖ ≤
    (1 / Real.sqrt (2 * Real.pi * t)) * ∫ y : ℝ, ‖φ y‖ := by

  show ‖∫ y : ℝ, schrodingerKernel1D t (x - y) * φ y‖ ≤ _

  calc ‖∫ y : ℝ, schrodingerKernel1D t (x - y) * φ y‖
      ≤ ∫ y : ℝ, ‖schrodingerKernel1D t (x - y) * φ y‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, ‖schrodingerKernel1D t (x - y)‖ * ‖φ y‖ := by
        congr 1; ext y; exact norm_mul _ _
    _ = ∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * t)) * ‖φ y‖ := by
        congr 1; ext y
        rw [schrodingerKernel1D_norm t (x - y) ht]
    _ = (1 / Real.sqrt (2 * Real.pi * t)) * ∫ y : ℝ, ‖φ y‖ :=
        integral_const_mul _ _

/-- **Theorem 2.1 (dispersive estimate, $n$D).** For $t > 0$,
$\|\psi(t, \cdot)\|_{L^\infty(\mathbb{R}^n)} \le (2\pi t)^{-n/2} \|\phi\|_{L^1(\mathbb{R}^n)}$. -/
theorem theorem_2_1_dispersive_estimate_nD {n : ℕ}
    (φ : Rn n → ℂ) (t : ℝ) (ht : 0 < t) (x : Rn n) :
    ‖schrodingerSolutionND φ t x‖ ≤
    (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) * ∫ y : Rn n, ‖φ y‖ := by
  show ‖∫ y : Rn n, schrodingerKernel t (x - y) * φ y‖ ≤ _
  calc ‖∫ y : Rn n, schrodingerKernel t (x - y) * φ y‖
      ≤ ∫ y : Rn n, ‖schrodingerKernel t (x - y) * φ y‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y : Rn n, ‖schrodingerKernel t (x - y)‖ * ‖φ y‖ := by
        congr 1; ext y; exact norm_mul _ _
    _ = ∫ y : Rn n, (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) * ‖φ y‖ := by
        congr 1; ext y
        rw [schrodingerKernel_norm t (x - y) ht]
    _ = (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) * ∫ y : Rn n, ‖φ y‖ :=
        integral_const_mul _ _

/-- **Theorem 2.1 (uniqueness, 1D).** Any two smooth solutions of the 1D free Schrödinger
equation that attain the same initial data $\phi$ as $t \to 0^+$ must agree at all $(t, x)$
with $t > 0$. -/
theorem theorem_2_1_uniqueness
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (ψ₁ ψ₂ : ℝ → ℝ → ℂ)
    (hψ₁ : IsFreeSchrodingerSolution ψ₁)
    (hψ₂ : IsFreeSchrodingerSolution ψ₂)
    (hψ₁_smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ψ₁ p.1 p.2))
    (hψ₂_smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ψ₂ p.1 p.2))
    (hψ₁_init : ∀ x, Filter.Tendsto (fun t => ψ₁ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)))
    (hψ₂_init : ∀ x, Filter.Tendsto (fun t => ψ₂ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)))
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ψ₁ t x = ψ₂ t x := by sorry

/-- Leibniz rule for the time derivative of the $n$D Schrödinger convolution: the time derivative
of $(K(t, \cdot) * \phi)(x)$ equals the convolution of $\partial_t K$ with $\phi$. -/
theorem leibniz_time_derivative_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Rn n) :
    deriv (fun s => schrodingerConvolutionND φ s x) t =
    ∫ y : Rn n, deriv (fun s => schrodingerKernel s (x - y)) t * φ y := by sorry

/-- Leibniz rule for the spatial Laplacian of the $n$D Schrödinger convolution: $\Delta_x$ of
$(K(t, \cdot) * \phi)(x)$ equals the convolution of $\Delta K$ with $\phi$. -/
theorem leibniz_laplacian_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Rn n) :
    complexLaplacian (schrodingerConvolutionND φ t) x =
    ∫ y : Rn n, complexLaplacian (schrodingerKernel t) (x - y) * φ y := by sorry

/-- Integrability of $\partial_t K(t, x - y) \cdot \phi(y)$ in $y$, needed to interchange the
time derivative and the integral. -/
theorem integrable_time_deriv_kernel_mul_phi {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Rn n) :
    Integrable (fun y => deriv (fun s => schrodingerKernel s (x - y)) t * φ y) := by sorry

/-- Integrability of $\Delta K(t, x - y) \cdot \phi(y)$ in $y$, needed to interchange the
spatial Laplacian and the integral. -/
theorem integrable_laplacian_kernel_mul_phi {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Rn n) :
    Integrable (fun y => complexLaplacian (schrodingerKernel t) (x - y) * φ y) := by sorry

/-- The Schrödinger differential operator commutes with the convolution integral:
$(i\partial_t + \tfrac{1}{2}\Delta)(K * \phi) = \int (i\partial_t K + \tfrac{1}{2}\Delta K)(x-y) \phi(y)\,d^n y$. -/
theorem leibniz_schrodinger_operator_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Rn n) :
    I * deriv (fun s => schrodingerConvolutionND φ s x) t +
    (1 / 2 : ℂ) * complexLaplacian (schrodingerConvolutionND φ t) x =
    ∫ y : Rn n, (I * deriv (fun s => schrodingerKernel s (x - y)) t +
    (1 / 2 : ℂ) * complexLaplacian (schrodingerKernel t) (x - y)) * φ y := by

  rw [leibniz_time_derivative_nD φ hφ_smooth hφ_supp t ht x,
      leibniz_laplacian_nD φ hφ_smooth hφ_supp t ht x]

  have h1 : I * ∫ y, deriv (fun s => schrodingerKernel s (x - y)) t * φ y =
      ∫ y, I * (deriv (fun s => schrodingerKernel s (x - y)) t * φ y) :=
    (integral_const_mul I _).symm
  have h2 : (1 / 2 : ℂ) * ∫ y, complexLaplacian (schrodingerKernel t) (x - y) * φ y =
      ∫ y, (1 / 2 : ℂ) * (complexLaplacian (schrodingerKernel t) (x - y) * φ y) :=
    (integral_const_mul (1 / 2 : ℂ) _).symm
  rw [h1, h2, ← integral_add
    ((integrable_time_deriv_kernel_mul_phi φ hφ_smooth hφ_supp t ht x).const_mul I)
    ((integrable_laplacian_kernel_mul_phi φ hφ_smooth hφ_supp t ht x).const_mul (1 / 2 : ℂ))]
  congr 1; ext y
  ring

/-- Combining the Leibniz rule with Lemma 2.0.2: in $n$ dimensions, the convolution
$(K(t, \cdot) * \phi)(x)$ solves the free Schrödinger equation for $t > 0$. -/
theorem differentiation_under_integral_schrodinger_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (x : Rn n) :
    I * deriv (fun s => schrodingerConvolutionND φ s x) t +
    (1 / 2 : ℂ) * complexLaplacian (schrodingerConvolutionND φ t) x = 0 := by

  rw [leibniz_schrodinger_operator_nD φ hφ_smooth hφ_supp t ht x]

  have hK : ∀ z : Rn n,
      I * deriv (fun s => schrodingerKernel s z) t +
      (1 / 2 : ℂ) * complexLaplacian (schrodingerKernel t) z = 0 :=
    lemma_2_0_2_K_solves_schrodinger_nD t ht
  simp_rw [hK, zero_mul, integral_zero]

/-- For $\phi \in C_c^\infty(\mathbb{R}^n)$, the $n$D Schrödinger convolution
$(t, x) \mapsto (K(t, \cdot) * \phi)(x)$ is $C^\infty$ jointly in $(t, x)$. -/
theorem smoothness_schrodinger_convolution_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
    ContDiff ℝ ⊤ (fun p : ℝ × Rn n => schrodingerConvolutionND φ p.1 p.2) := by sorry

/-- **Theorem 2.1 (existence, $n$D).** The candidate solution $\psi = K(t, \cdot) * \phi$ solves
the $n$-dimensional free Schrödinger equation for $t > 0$. -/
theorem theorem_2_1_solves_equation_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
    IsFreeSchrodingerSolutionND (schrodingerSolutionND φ) := by
  intro t ht x
  exact differentiation_under_integral_schrodinger_nD φ hφ_smooth hφ_supp t ht x

/-- **Theorem 2.1 (initial data, $n$D).** The candidate solution $\psi$ attains the initial data
$\phi$ as $t \to 0^+$, for $\phi \in C_c^\infty(\mathbb{R}^n)$. -/
theorem theorem_2_1_initial_data_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (x : Rn n) :
    Filter.Tendsto (fun t => schrodingerSolutionND φ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)) :=
  proposition_2_0_3_initial_data_recovery_nD φ hφ_smooth hφ_supp x

/-- **Theorem 2.1 (smoothness, $n$D).** The solution $\psi(t, x)$ is smooth in $(t, x)$. -/
theorem theorem_2_1_smoothness_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
    ContDiff ℝ ⊤ (fun p : ℝ × Rn n => schrodingerSolutionND φ p.1 p.2) :=
  smoothness_schrodinger_convolution_nD φ hφ_smooth hφ_supp

/-- **Theorem 2.1 (uniqueness, $n$D).** Any two smooth solutions of the $n$-dimensional free
Schrödinger equation that attain the same initial data $\phi$ as $t \to 0^+$ must agree at all
$(t, x)$ with $t > 0$. -/
theorem theorem_2_1_uniqueness_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (ψ₁ ψ₂ : ℝ → Rn n → ℂ)
    (hψ₁ : IsFreeSchrodingerSolutionND ψ₁)
    (hψ₂ : IsFreeSchrodingerSolutionND ψ₂)
    (hψ₁_smooth : ContDiff ℝ ⊤ (fun p : ℝ × Rn n => ψ₁ p.1 p.2))
    (hψ₂_smooth : ContDiff ℝ ⊤ (fun p : ℝ × Rn n => ψ₂ p.1 p.2))
    (hψ₁_init : ∀ x, Filter.Tendsto (fun t => ψ₁ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)))
    (hψ₂_init : ∀ x, Filter.Tendsto (fun t => ψ₂ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x)))
    (t : ℝ) (ht : 0 < t) (x : Rn n) :
    ψ₁ t x = ψ₂ t x := by sorry

/-- **Theorem 2.1 (full statement, $n$D).** For $\phi \in C_c^\infty(\mathbb{R}^n)$ there exists a
unique smooth solution $\psi \in C^\infty((0, \infty) \times \mathbb{R}^n)$ to the free Schrödinger
equation with $\psi(0, x) = \phi(x)$, given by $\psi(t, x) = (K(t, \cdot) * \phi)(x)$, and
$\psi$ satisfies the dispersive estimate
$\|\psi(t, \cdot)\|_{L^\infty} \le C t^{-n/2} \|\phi\|_{L^1}$. -/
theorem theorem_2_1_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ) :
    IsFreeSchrodingerSolutionND (schrodingerSolutionND φ) ∧
    (∀ x, Filter.Tendsto (fun t => schrodingerSolutionND φ t x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x))) ∧
    ContDiff ℝ ⊤ (fun p : ℝ × Rn n => schrodingerSolutionND φ p.1 p.2) ∧
    (∀ t > 0, ∀ x, ‖schrodingerSolutionND φ t x‖ ≤
      (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) * ∫ y : Rn n, ‖φ y‖) ∧
    (∀ (ψ₁ ψ₂ : ℝ → Rn n → ℂ),
      IsFreeSchrodingerSolutionND ψ₁ →
      IsFreeSchrodingerSolutionND ψ₂ →
      ContDiff ℝ ⊤ (fun p : ℝ × Rn n => ψ₁ p.1 p.2) →
      ContDiff ℝ ⊤ (fun p : ℝ × Rn n => ψ₂ p.1 p.2) →
      (∀ x, Filter.Tendsto (fun t => ψ₁ t x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x))) →
      (∀ x, Filter.Tendsto (fun t => ψ₂ t x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ x))) →
      ∀ t > 0, ∀ x, ψ₁ t x = ψ₂ t x) :=
  ⟨theorem_2_1_solves_equation_nD φ hφ_smooth hφ_supp,
   theorem_2_1_initial_data_nD φ hφ_smooth hφ_supp,
   theorem_2_1_smoothness_nD φ hφ_smooth hφ_supp,
   fun t ht x => theorem_2_1_dispersive_estimate_nD φ t ht x,
   fun ψ₁ ψ₂ h1 h2 h3 h4 h5 h6 t ht x =>
     theorem_2_1_uniqueness_nD φ hφ_smooth hφ_supp ψ₁ ψ₂ h1 h2 h3 h4 h5 h6 t ht x⟩

/-- The Fourier multiplier $\hat{K}(t, \xi) = e^{-2\pi^2 i t \xi^2}$ has modulus $1$, so the
Fourier transform of the solution has the same pointwise modulus as $\hat{\phi}$:
$|\hat{\psi}(t, \xi)| = |\hat{\phi}(\xi)|$. -/
theorem fourier_solution_norm_sq_eq
    (φ : ℝ → ℂ) (t ξ : ℝ) :
    ‖solutionFT φ t ξ‖ = ‖CM16.fourierTransform φ ξ‖ := by
  unfold solutionFT
  rw [norm_mul]
  simp only [fundamentalSolutionFT, norm_exp_ofReal_mul_I, one_mul]

/-- The custom Fourier transform defined in CM16 agrees with Mathlib's Fourier transform $\mathcal{F}$. -/
lemma fourierTransform_eq_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    CM16.fourierTransform f ξ = 𝓕 f ξ :=
  CM16.fourierTransform_eq_mathlib_fourier f ξ

set_option maxHeartbeats 400000 in
/-- **Plancherel's theorem** for compactly supported smooth functions in 1D:
$\int_{\mathbb{R}} |f(x)|^2\,dx = \int_{\mathbb{R}} |\hat{f}(\xi)|^2\,d\xi$. -/
theorem plancherel_theorem
    (f : ℝ → ℂ) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    ∫ x, ‖f x‖ ^ 2 = ∫ ξ, ‖CM16.fourierTransform f ξ‖ ^ 2 := by
  have hf_smooth' : ContDiff ℝ (↑(⊤ : ℕ∞)) f := hf_smooth.of_le le_top
  let sf : SchwartzMap ℝ ℂ := hf_supp.toSchwartzMap hf_smooth'
  have h_eq_f : ∀ x, sf x = f x := HasCompactSupport.toSchwartzMap_toFun hf_supp hf_smooth'
  have h := SchwartzMap.integral_norm_sq_fourier sf

  have hlhs : ∫ ξ : ℝ, ‖(𝓕 sf) ξ‖ ^ 2 = ∫ ξ, ‖CM16.fourierTransform f ξ‖ ^ 2 := by
    congr 1; ext ξ
    show ‖𝓕 (⇑sf) ξ‖ ^ 2 = ‖CM16.fourierTransform f ξ‖ ^ 2
    rw [show (⇑sf : ℝ → ℂ) = f from funext h_eq_f,
        show 𝓕 f ξ = CM16.fourierTransform f ξ from (fourierTransform_eq_fourier f ξ).symm]

  have hrhs : ∫ x : ℝ, ‖sf x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    apply integral_congr_ae; filter_upwards with x; rw [h_eq_f x]
  linarith

/-- The Fourier transform of the 1D Schrödinger convolution equals the multiplier representation:
$\widehat{K(t, \cdot) * \phi}(\xi) = \hat{K}(t, \xi) \hat{\phi}(\xi)$. -/
theorem FT_of_convolution_solution
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (ξ : ℝ) :
    CM16.fourierTransform (schrodingerConvolution φ t) ξ = solutionFT φ t ξ := by sorry

/-- **Proposition 2.0.4 (Preservation of $L^2$ norm, 1D).** Under the assumptions of Theorem 2.1,
$\|\psi(t, \cdot)\|_{L^2} = \|\phi\|_{L^2}$ for all $t > 0$. The proof goes through Plancherel
and the fact that the Fourier multiplier has unit modulus. -/
theorem proposition_2_0_4_L2_preservation
    (φ : ℝ → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t)
    (hψ_plancherel : ∫ x, ‖schrodingerConvolution φ t x‖ ^ 2 =
      ∫ ξ, ‖CM16.fourierTransform (schrodingerConvolution φ t) ξ‖ ^ 2) :
    ∫ x : ℝ, ‖schrodingerSolution φ t x‖ ^ 2 =
    ∫ x : ℝ, ‖φ x‖ ^ 2 := by

  show ∫ x, ‖schrodingerConvolution φ t x‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2

  rw [hψ_plancherel]

  have step12 : ∀ ξ, ‖CM16.fourierTransform (schrodingerConvolution φ t) ξ‖ =
      ‖CM16.fourierTransform φ ξ‖ := by
    intro ξ
    rw [FT_of_convolution_solution φ hφ_smooth hφ_supp t ht ξ]
    exact fourier_solution_norm_sq_eq φ t ξ

  have step3 : ∫ ξ, ‖CM16.fourierTransform (schrodingerConvolution φ t) ξ‖ ^ 2 =
      ∫ ξ, ‖CM16.fourierTransform φ ξ‖ ^ 2 := by
    congr 1; ext ξ; rw [step12 ξ]

  rw [step3, ← plancherel_theorem φ hφ_smooth hφ_supp]

/-- The $n$-dimensional Fourier transform $\hat{f}(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i \langle \xi, x \rangle}\,d^n x$. -/
def fourierTransformRn {n : ℕ} (f : Rn n → ℂ) (ξ : Rn n) : ℂ :=
  ∫ x : Rn n, f x * Complex.exp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I)

/-- The Fourier transform of the $n$D Schrödinger fundamental solution:
$\hat{K}(t, \xi) = e^{-2\pi^2 i t |\xi|^2}$. -/
def fundamentalSolutionFT_nD {n : ℕ} (t : ℝ) (ξ : Rn n) : ℂ :=
  exp (((-2 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) : ℂ) * I)

/-- The Fourier transform of the $n$D free Schrödinger solution with initial data $\phi$:
$\hat{\psi}(t, \xi) = \hat{K}(t, \xi) \hat{\phi}(\xi)$. -/
def solutionFT_nD {n : ℕ} (φ : Rn n → ℂ) (t : ℝ) (ξ : Rn n) : ℂ :=
  fundamentalSolutionFT_nD t ξ * fourierTransformRn φ ξ

/-- The $n$D analogue: the modulus of the Fourier transform of the solution equals that of
$\hat{\phi}$, since the Fourier multiplier $\hat{K}(t, \xi)$ has unit modulus. -/
theorem fourier_solution_norm_sq_eq_nD {n : ℕ}
    (φ : Rn n → ℂ) (t : ℝ) (ξ : Rn n) :
    ‖solutionFT_nD φ t ξ‖ = ‖fourierTransformRn φ ξ‖ := by
  unfold solutionFT_nD
  rw [norm_mul]
  simp only [fundamentalSolutionFT_nD, norm_exp_ofReal_mul_I, one_mul]

/-- The custom $n$D Fourier transform agrees with Mathlib's Fourier transform $\mathcal{F}$ on
$\mathbb{R}^n$. -/
lemma fourierTransformRn_eq_fourier {n : ℕ} (f : Rn n → ℂ) (ξ : Rn n) :
    fourierTransformRn f ξ = 𝓕 f ξ := by
  unfold fourierTransformRn; rw [Real.fourier_eq']
  congr 1; ext x
  simp only [smul_eq_mul, mul_comm (cexp _) (f x)]
  congr 1; rw [real_inner_comm ξ x]

set_option maxHeartbeats 400000 in
/-- **Plancherel's theorem** for compactly supported smooth functions in $\mathbb{R}^n$:
$\int |f(x)|^2\,d^n x = \int |\hat{f}(\xi)|^2\,d^n \xi$. -/
theorem plancherel_compact_support_nD {n : ℕ}
    (f : Rn n → ℂ) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    ∫ x : Rn n, ‖f x‖ ^ 2 = ∫ ξ : Rn n, ‖fourierTransformRn f ξ‖ ^ 2 := by
  have hf_smooth' : ContDiff ℝ (↑(⊤ : ℕ∞)) f := hf_smooth.of_le le_top
  let sf : SchwartzMap (Rn n) ℂ := hf_supp.toSchwartzMap hf_smooth'
  have h_eq_f : ∀ x, sf x = f x := HasCompactSupport.toSchwartzMap_toFun hf_supp hf_smooth'
  have h := SchwartzMap.integral_norm_sq_fourier sf

  have hlhs : ∫ ξ : Rn n, ‖(𝓕 sf) ξ‖ ^ 2 = ∫ ξ, ‖fourierTransformRn f ξ‖ ^ 2 := by
    congr 1; ext ξ
    show ‖𝓕 (⇑sf) ξ‖ ^ 2 = ‖fourierTransformRn f ξ‖ ^ 2
    rw [show (⇑sf : Rn n → ℂ) = f from funext h_eq_f,
        show 𝓕 f ξ = fourierTransformRn f ξ from (fourierTransformRn_eq_fourier f ξ).symm]

  have hrhs : ∫ x : Rn n, ‖sf x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    apply integral_congr_ae; filter_upwards with x; rw [h_eq_f x]
  linarith

/-- Fubini-style swap of the order of integration in the double integral arising in computing
$\widehat{K(t, \cdot) * \phi}(\xi)$. -/
theorem integral_swap_convolution_FT_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (ξ : Rn n) :
    ∫ (x : Rn n), ∫ (y : Rn n),
      schrodingerKernel t (x - y) * φ y *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) =
    ∫ (y : Rn n), ∫ (x : Rn n),
      schrodingerKernel t (x - y) * φ y *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) := by sorry

/-- Rearrangement (via Fubini) of the Fourier transform of the convolution as an iterated
integral with $\phi$ outside and the kernel integrated against the Fourier exponential. -/
theorem fubini_integrability_convolution_FT_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (ξ : Rn n) :
    ∫ (x : Rn n), (∫ (y : Rn n), schrodingerKernel t (x - y) * φ y) *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) =
    ∫ (y : Rn n), φ y *
      ∫ (x : Rn n), schrodingerKernel t (x - y) *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) := by

  have step1 : ∫ (x : Rn n), (∫ (y : Rn n), schrodingerKernel t (x - y) * φ y) *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) =
    ∫ (x : Rn n), ∫ (y : Rn n),
      schrodingerKernel t (x - y) * φ y *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) := by
    congr 1; ext x; symm
    exact integral_mul_const (cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I))
      (fun y => schrodingerKernel t (x - y) * φ y)
  rw [step1]

  rw [integral_swap_convolution_FT_nD φ hφ_smooth hφ_supp t ht ξ]

  congr 1; ext y
  have rearrange : ∀ x : Rn n,
    schrodingerKernel t (x - y) * φ y *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) =
    φ y * (schrodingerKernel t (x - y) *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I)) := by
    intro x; ring
  simp_rw [rearrange]
  exact integral_const_mul (φ y) _

/-- Translation property of the Fourier transform applied to the Schrödinger kernel:
$\int K(t, x - y) e^{-2\pi i \langle \xi, x\rangle}\,d^n x = e^{-2\pi i \langle \xi, y\rangle} \hat{K}(t, \xi)$. -/
theorem FT_kernel_translation_nD {n : ℕ}
    (t : ℝ) (ht : 0 < t) (ξ y : Rn n) :
    ∫ (x : Rn n), schrodingerKernel t (x - y) *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) =
    cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ y) * I) *
      fourierTransformRn (schrodingerKernel t) ξ := by

  have subst : ∫ (x : Rn n), schrodingerKernel t (x - y) *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) =
    ∫ (u : Rn n), schrodingerKernel t u *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I) := by
    rw [show (fun x => schrodingerKernel t (x - y) *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I)) =
      (fun x => (fun u => schrodingerKernel t u *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I)) (x - y)) from by
      ext x; congr 1; congr 1; congr 1; congr 1; congr 1; rw [sub_add_cancel]]
    exact integral_sub_right_eq_self
      (fun u => schrodingerKernel t u *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I)) y
  rw [subst]

  have inner_split : ∀ u : Rn n,
    schrodingerKernel t u *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I) =
    cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I) *
    (schrodingerKernel t u *
      cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I)) := by
    intro u
    rw [inner_add_right]
    have : ((-2 * Real.pi * (@inner ℝ (Rn n) _ ξ u + @inner ℝ (Rn n) _ ξ y) : ℝ) : ℂ) * I =
      ((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I +
      ((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_add]; ring
  simp_rw [inner_split]

  simp_rw [show ∀ u : Rn n,
    cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I) *
    (schrodingerKernel t u *
      cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I)) =
    cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I) •
    (schrodingerKernel t u *
      cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I)) from by
    intro u; rw [smul_eq_mul]]
  rw [integral_smul, smul_eq_mul]
  rfl

/-- The squared Euclidean norm equals the sum of coordinate squares: $\|\xi\|^2 = \sum_i \xi_i^2$. -/
lemma norm_sq_eq_sum_sq_real {n : ℕ} (ξ : Rn n) :
    ∑ i : Fin n, (ξ i) ^ 2 = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  congr 1; simp [Real.norm_eq_abs, sq_abs]

/-- The Fourier transform of the 1D complex Gaussian
$\frac{1}{(2\pi i t)^{1/2}} e^{i u^2 / (2t)}$ at frequency $\xi$ equals
$e^{-2\pi^2 i t \xi^2}$. -/
theorem FT_complex_gaussian_1D (t : ℝ) (ht : 0 < t) (ξ_i : ℝ) :
    ∫ u : ℝ, ((((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(1 : ℂ) / 2) *
      cexp (I * ((u ^ 2 / (2 * t) : ℝ) : ℂ))) *
      cexp (((-2 * Real.pi * ξ_i * u : ℝ) : ℂ) * I) =
    cexp (((-2 * Real.pi ^ 2 * t * ξ_i ^ 2 : ℝ) : ℂ) * I) := by sorry

/-- Factorization of the $n$D Fourier transform of $K(t, \cdot)$ as a product of 1D Fourier
transforms of complex Gaussians, via Fubini and the product structure of $K$. -/
theorem FT_gaussian_nD_fubini {n : ℕ} (t : ℝ) (ht : 0 < t) (ξ : Rn n) :
    fourierTransformRn (schrodingerKernel t) ξ =
    ∏ i : Fin n, (∫ u : ℝ, ((((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(1 : ℂ) / 2) *
      cexp (I * ((u ^ 2 / (2 * t) : ℝ) : ℂ))) *
      cexp (((-2 * Real.pi * (ξ i) * u : ℝ) : ℂ) * I)) := by sorry

/-- The $n$D Fourier transform of the Schrödinger kernel agrees with the closed-form
multiplier: $\hat{K}(t, \xi) = e^{-2\pi^2 i t |\xi|^2}$. -/
theorem FT_of_schrodinger_kernel_nD {n : ℕ}
    (t : ℝ) (ht : 0 < t) (ξ : Rn n) :
    fourierTransformRn (schrodingerKernel t) ξ = fundamentalSolutionFT_nD t ξ := by

  rw [FT_gaussian_nD_fubini t ht ξ]

  simp_rw [FT_complex_gaussian_1D t ht]

  simp only [fundamentalSolutionFT_nD]
  rw [← Complex.exp_sum]
  congr 1

  have h : (-2 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) =
      ∑ i : Fin n, (-2 * Real.pi ^ 2 * t * (ξ i) ^ 2 : ℝ) := by
    rw [← norm_sq_eq_sum_sq_real ξ]
    simp [Finset.mul_sum]
  rw [h]
  push_cast
  simp [Finset.sum_mul]

/-- The Fourier transform of the $n$D Schrödinger convolution equals the multiplier
representation: $\widehat{K(t, \cdot) * \phi}(\xi) = \hat{K}(t, \xi) \hat{\phi}(\xi)$. -/
theorem FT_of_convolution_solution_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) (ξ : Rn n) :
    fourierTransformRn (schrodingerConvolutionND φ t) ξ = solutionFT_nD φ t ξ := by

  simp only [fourierTransformRn, schrodingerConvolutionND, solutionFT_nD, fundamentalSolutionFT_nD]

  rw [fubini_integrability_convolution_FT_nD φ hφ_smooth hφ_supp t ht ξ]


  simp_rw [FT_kernel_translation_nD t ht ξ]

  simp_rw [FT_of_schrodinger_kernel_nD t ht ξ, fundamentalSolutionFT_nD]

  have h : ∀ y : Rn n,
    φ y * (cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I) *
      cexp (((-2 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) : ℂ) * I)) =
    cexp (((-2 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) : ℂ) * I) •
      (φ y * cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I)) := by
    intro y; rw [smul_eq_mul]; ring
  simp_rw [h, integral_smul, smul_eq_mul]

/-- For fixed $t > 0$, the function $x \mapsto (K(t, \cdot) * \phi)(x)$ is $C^\infty$ in $x$,
deduced from the joint smoothness in $(t, x)$. -/
theorem schrodingerConvolutionND_smooth {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ⊤ (schrodingerConvolutionND φ t) := by


  have hj := smoothness_schrodinger_convolution_nD φ hφ_smooth hφ_supp
  have heq : schrodingerConvolutionND φ t =
      (fun p : ℝ × Rn n => schrodingerConvolutionND φ p.1 p.2) ∘ (fun x => (t, x)) := by
    ext x; simp
  rw [heq]
  exact hj.comp (contDiff_prodMk_right t)

/-- Identification of the Schrödinger convolution with the action of the Fourier multiplier
$\hat{K}(t, \cdot)$ on the Schwartz function $\phi$: as functions, the convolution equals the
Fourier-multiplier composition. -/
theorem convolution_eq_fourierMultiplier {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    (fun x => (SchwartzMap.fourierMultiplierCLM ℂ (fundamentalSolutionFT_nD t)
        (hφ_supp.toSchwartzMap (hφ_smooth.of_le le_top))) x) =
      schrodingerConvolutionND φ t := by sorry

/-- Schwartz-type decay for the $n$D Schrödinger convolution: for every $k, m \in \mathbb{N}$
there is a constant $C$ with $\|x\|^k \|D^m (K * \phi)(x)\| \le C$. -/
theorem schrodingerConvolutionND_decay {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    ∀ (k m : ℕ), ∃ C, ∀ x : Rn n,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (schrodingerConvolutionND φ t) x‖ ≤ C := by

  let φ_s : SchwartzMap (Rn n) ℂ := hφ_supp.toSchwartzMap (hφ_smooth.of_le le_top)
  let result : SchwartzMap (Rn n) ℂ :=
    SchwartzMap.fourierMultiplierCLM ℂ (fundamentalSolutionFT_nD t) φ_s

  have hfun : (fun x => result x) = schrodingerConvolutionND φ t :=
    convolution_eq_fourierMultiplier φ hφ_smooth hφ_supp t ht
  have hfun' : result.toFun = schrodingerConvolutionND φ t := by
    ext x; exact congr_fun hfun x

  intro k m
  obtain ⟨C, hC⟩ := result.decay' k m
  refine ⟨C, fun x => ?_⟩
  rw [← hfun']
  exact hC x

/-- Promotion of $x \mapsto (K(t, \cdot) * \phi)(x)$ to a Schwartz function, packaging the
smoothness and Schwartz-decay results. -/
noncomputable def convolution_solution_schwartz_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    { sf : SchwartzMap (Rn n) ℂ // ∀ x, sf x = schrodingerConvolutionND φ t x } :=
  ⟨SchwartzMap.mk (schrodingerConvolutionND φ t)
    ((schrodingerConvolutionND_smooth φ hφ_smooth hφ_supp t ht).of_le le_top)
    (schrodingerConvolutionND_decay φ hφ_smooth hφ_supp t ht),
   fun x => rfl⟩

set_option maxHeartbeats 400000 in
/-- Plancherel's theorem applied to the $n$D Schrödinger convolution, viewed as a Schwartz
function: $\int \|(K(t,\cdot) * \phi)(x)\|^2\,d^n x = \int \|\widehat{K(t, \cdot) * \phi}(\xi)\|^2\,d^n \xi$. -/
theorem plancherel_convolution_solution_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    ∫ x : Rn n, ‖schrodingerConvolutionND φ t x‖ ^ 2 =
    ∫ ξ : Rn n, ‖fourierTransformRn (schrodingerConvolutionND φ t) ξ‖ ^ 2 := by

  obtain ⟨sf, h_eq⟩ := convolution_solution_schwartz_nD φ hφ_smooth hφ_supp t ht

  have h := SchwartzMap.integral_norm_sq_fourier sf

  have hlhs : ∫ ξ : Rn n, ‖(𝓕 sf) ξ‖ ^ 2 =
      ∫ ξ, ‖fourierTransformRn (schrodingerConvolutionND φ t) ξ‖ ^ 2 := by
    congr 1; ext ξ
    show ‖𝓕 (⇑sf) ξ‖ ^ 2 = ‖fourierTransformRn (schrodingerConvolutionND φ t) ξ‖ ^ 2
    rw [show (⇑sf : Rn n → ℂ) = schrodingerConvolutionND φ t from funext h_eq,
        show 𝓕 (schrodingerConvolutionND φ t) ξ =
          fourierTransformRn (schrodingerConvolutionND φ t) ξ from
          (fourierTransformRn_eq_fourier (schrodingerConvolutionND φ t) ξ).symm]

  have hrhs : ∫ x : Rn n, ‖sf x‖ ^ 2 =
      ∫ x, ‖schrodingerConvolutionND φ t x‖ ^ 2 := by
    apply integral_congr_ae; filter_upwards with x; rw [h_eq x]
  linarith

set_option maxHeartbeats 400000 in

/-- The Fourier-side proof of $L^2$-norm preservation in $n$ dimensions: using Plancherel and
the fact that $\hat{K}$ has unit modulus,
$\int \|(K(t, \cdot) * \phi)(x)\|^2\,d^n x = \int \|\phi(x)\|^2\,d^n x$. -/
theorem L2_norm_preservation_nD_fourier_proof {n : ℕ}
    (φ : Rn n → ℂ)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    ∫ x : Rn n, ‖schrodingerConvolutionND φ t x‖ ^ 2 =
    ∫ x : Rn n, ‖φ x‖ ^ 2 := by

  rw [plancherel_convolution_solution_nD φ hφ_smooth hφ_supp t ht]

  have step12 : ∀ ξ, ‖fourierTransformRn (schrodingerConvolutionND φ t) ξ‖ =
      ‖fourierTransformRn φ ξ‖ := by
    intro ξ
    rw [FT_of_convolution_solution_nD φ hφ_smooth hφ_supp t ht ξ]
    exact fourier_solution_norm_sq_eq_nD φ t ξ

  have step3 : ∫ ξ : Rn n, ‖fourierTransformRn (schrodingerConvolutionND φ t) ξ‖ ^ 2 =
      ∫ ξ : Rn n, ‖fourierTransformRn φ ξ‖ ^ 2 := by
    congr 1; ext ξ; rw [step12 ξ]

  rw [step3, ← plancherel_compact_support_nD φ hφ_smooth hφ_supp]

/-- **Proposition 2.0.4 (Preservation of $L^2$ norm, $n$D).** Under the assumptions of
Theorem 2.1, $\|\psi(t, \cdot)\|_{L^2(\mathbb{R}^n)} = \|\phi\|_{L^2(\mathbb{R}^n)}$. In
particular, if $\phi$ is a unit-mass wave function, then $\psi(t, \cdot)$ remains so for all
$t > 0$. -/
theorem proposition_2_0_4_L2_preservation_nD {n : ℕ}
    (φ : Rn n → ℂ) (hφ_smooth : ContDiff ℝ ⊤ φ) (hφ_supp : HasCompactSupport φ)
    (t : ℝ) (ht : 0 < t) :
    ∫ x : Rn n, ‖schrodingerSolutionND φ t x‖ ^ 2 =
    ∫ x : Rn n, ‖φ x‖ ^ 2 := by

  show ∫ x : Rn n, ‖schrodingerConvolutionND φ t x‖ ^ 2 = ∫ x : Rn n, ‖φ x‖ ^ 2
  exact L2_norm_preservation_nD_fourier_proof φ hφ_smooth hφ_supp t ht

end SchrodingerEquation
