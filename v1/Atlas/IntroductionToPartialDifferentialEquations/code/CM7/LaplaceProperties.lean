/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.HaarToSphere

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic
open Set Metric MeasureTheory Topology Filter

noncomputable section

namespace CM7

/-- A `PDEDomain` in $\mathbb{R}^n$ is a connected open subset, the natural setting in
which to pose boundary-value problems for PDEs. -/
structure PDEDomain (n : ℕ) where
  carrier : Set (Fin n → ℝ)
  isOpen : IsOpen carrier
  isConnected : IsConnected carrier

/-- The Laplacian $\Delta u(x) = \sum_{i=1}^n \partial_i^2 u(x)$ of a function
$u : \mathbb{R}^n \to \mathbb{R}$, defined using iterated Fréchet derivatives applied to the
standard basis vectors $e_i$. -/
noncomputable def Laplacian (n : ℕ) (u : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x (Pi.single i 1)

/-- Linearity of the Laplacian under subtraction: for $C^2$ functions $u, v$ on an open
set $\Omega$, we have $\Delta(u - v)(x) = \Delta u(x) - \Delta v(x)$ at every $x \in \Omega$. -/
theorem laplacian_sub {n : ℕ} {u v : (Fin n → ℝ) → ℝ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    Laplacian n (fun x => u x - v x) x = Laplacian n u x - Laplacian n v x := by

  have hu_diff : ∀ᶠ y in nhds x, DifferentiableAt ℝ u y := by
    have : DifferentiableOn ℝ u Ω := hu.differentiableOn (by norm_num)
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact this.differentiableAt (hΩ.mem_nhds hy)
  have hv_diff : ∀ᶠ y in nhds x, DifferentiableAt ℝ v y := by
    have : DifferentiableOn ℝ v Ω := hv.differentiableOn (by norm_num)
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact this.differentiableAt (hΩ.mem_nhds hy)

  have hu2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x := by
    intro i
    have : ContDiffOn ℝ (1 + 1) u Ω := by exact_mod_cast hu
    have h_fderiv_diff : DifferentiableOn ℝ (fderiv ℝ u) Ω :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp this).2.2.differentiableOn (by norm_num)
    exact (h_fderiv_diff.differentiableAt (hΩ.mem_nhds hx)).clm_apply (differentiableAt_const _)
  have hv2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ v y (Pi.single i 1)) x := by
    intro i
    have : ContDiffOn ℝ (1 + 1) v Ω := by exact_mod_cast hv
    have h_fderiv_diff : DifferentiableOn ℝ (fderiv ℝ v) Ω :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp this).2.2.differentiableOn (by norm_num)
    exact (h_fderiv_diff.differentiableAt (hΩ.mem_nhds hx)).clm_apply (differentiableAt_const _)

  simp only [Laplacian]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext i

  have h_inner : ∀ᶠ y in nhds x, fderiv ℝ (fun z => u z - v z) y (Pi.single i 1) =
      fderiv ℝ u y (Pi.single i 1) - fderiv ℝ v y (Pi.single i 1) := by
    filter_upwards [hu_diff, hv_diff] with y hy_u hy_v
    rw [fderiv_fun_sub hy_u hy_v, ContinuousLinearMap.sub_apply]

  rw [Filter.EventuallyEq.fderiv_eq h_inner]

  rw [fderiv_fun_sub (hu2 i) (hv2 i)]
  simp [ContinuousLinearMap.sub_apply]

/-- The Laplacian commutes with negation: $\Delta(-u) = -\Delta u$. -/
theorem laplacian_neg {n : ℕ} (u : (Fin n → ℝ) → ℝ) :
    Laplacian n (fun x => -u x) = fun x => -Laplacian n u x := by
  ext x
  simp only [Laplacian, ← Finset.sum_neg_distrib]
  congr 1
  ext i
  have h1 : ∀ y, fderiv ℝ (fun x => -u x) y = -fderiv ℝ u y := fun y => fderiv_fun_neg
  simp_rw [h1, ContinuousLinearMap.neg_apply]
  rw [fderiv_fun_neg]
  simp

/-- The Laplacian of a constant function is identically zero: $\Delta c = 0$. -/
theorem laplacian_const {n : ℕ} (c : ℝ) :
    Laplacian n (fun _ : Fin n → ℝ => c) = fun _ => 0 := by
  ext x
  simp only [Laplacian]
  apply Finset.sum_eq_zero
  intro i _
  have h1 : ∀ y : Fin n → ℝ, fderiv ℝ (fun _ : Fin n → ℝ => c) y = 0 :=
    fun y => fderiv_const_apply c
  simp_rw [h1]
  simp [fderiv_const_apply]

/-- A function $u : \mathbb{R}^n \to \mathbb{R}$ is harmonic on an open set $\Omega$ if it
is $C^2$ on $\Omega$ and satisfies Laplace's equation $\Delta u(x) = 0$ for all $x \in \Omega$. -/
structure IsHarmonic {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop where
  contDiffOn : ContDiffOn ℝ 2 u Ω
  laplacian_eq_zero : ∀ x ∈ Ω, Laplacian n u x = 0

/-- The predicate that $u$ solves Poisson's equation $\Delta u = f$ on $\Omega$, i.e. for
every $x \in \Omega$, $\Delta u(x) = f(x)$. -/
def IsPoisson {n : ℕ} (u : (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (Ω : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ Ω, Laplacian n u x = f x

/-- A harmonic function is $C^2$ on its domain. -/
theorem harmonic_is_contDiffOn {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : IsHarmonic u Ω) :
    ContDiffOn ℝ 2 u Ω :=
  hu.contDiffOn

/-- The difference of two harmonic functions on an open set is harmonic. -/
lemma IsHarmonic.sub {n : ℕ} {u v : (Fin n → ℝ) → ℝ} {Ω : Set (Fin n → ℝ)}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω) (hv : IsHarmonic v Ω) :
    IsHarmonic (fun x => u x - v x) Ω where
  contDiffOn := hu.contDiffOn.sub hv.contDiffOn
  laplacian_eq_zero := by
    intro x hx
    rw [laplacian_sub hΩ hu.contDiffOn hv.contDiffOn hx]
    rw [hu.laplacian_eq_zero x hx, hv.laplacian_eq_zero x hx, sub_self]

/-- The negation of a harmonic function is harmonic. -/
lemma IsHarmonic.neg {n : ℕ} {u : (Fin n → ℝ) → ℝ} {Ω : Set (Fin n → ℝ)}
    (hu : IsHarmonic u Ω) :
    IsHarmonic (fun x => -u x) Ω where
  contDiffOn := hu.contDiffOn.neg
  laplacian_eq_zero := by
    intro x hx
    simp [laplacian_neg, hu.laplacian_eq_zero x hx]

/-- The Dirichlet energy $\int_\Omega \|\nabla u(x)\|^2\, dx$ of $u$ on $\Omega$. -/
noncomputable def gradNormSquaredIntegral {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : ℝ :=
  ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2

/-- The outward unit normal vector field on the boundary of a domain in $\mathbb{R}^n$.
Provided abstractly as an opaque function. -/
opaque outwardUnitNormal (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ)

/-- The surface (boundary) measure on $\partial \Omega$ for a domain $\Omega \subseteq \mathbb{R}^n$,
provided abstractly as an opaque measure. -/
opaque surfaceMeasure (n : ℕ) (Ω : Set (Fin n → ℝ)) : Measure (Fin n → ℝ)

/-- The outward normal derivative $\partial_\nu w(x) = \nabla w(x) \cdot \nu(x)$ at a boundary
point $x$, where $\nu$ is the outward unit normal. -/
def NormalDerivative (n : ℕ) (w : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ w x (outwardUnitNormal n x)

/-- The boundary energy integral $\int_{\partial \Omega} w(x) \, \partial_\nu w(x) \, dS$
arising from Green's first identity. -/
def boundaryEnergyIntegral {n : ℕ} (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : ℝ :=
  ∫ x in frontier Ω, w x * NormalDerivative n w x ∂(surfaceMeasure n Ω)

/-- Green's first identity for a bounded open set $\Omega$:
$\int_\Omega \|\nabla w\|^2 + \int_\Omega w \, \Delta w = \int_{\partial \Omega} w \, \partial_\nu w \, dS$. -/
theorem greens_first_identity {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) :
    gradNormSquaredIntegral w Ω + (∫ x in Ω, w x * Laplacian n w x) =
      boundaryEnergyIntegral w Ω := by sorry

/-- Rearranged form of Green's first identity:
$\int_\Omega w \, \Delta w = -\int_\Omega \|\nabla w\|^2 + \int_{\partial \Omega} w \, \partial_\nu w \, dS$. -/
theorem energy_identity {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) :
    (∫ x in Ω, w x * Laplacian n w x) =
      -gradNormSquaredIntegral w Ω + boundaryEnergyIntegral w Ω := by
  have h := greens_first_identity w Ω hΩ hΩb
  linarith

/-- The Dirichlet energy $\int_\Omega \|\nabla w\|^2$ is nonnegative. -/
theorem gradNormSquaredIntegral_nonneg {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) :
    gradNormSquaredIntegral w Ω ≥ 0 := by
  simp only [gradNormSquaredIntegral, ge_iff_le]
  apply integral_nonneg
  intro x; positivity

/-- If the Fréchet derivative of $w$ is continuous on $\overline{\Omega}$ and $\Omega$ is bounded,
then $\|\nabla w\|^2$ is integrable on $\Omega$. -/
theorem gradNormSquared_integrableOn {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω)) :
    IntegrableOn (fun x => ‖fderiv ℝ w x‖ ^ 2) Ω := by
  have hK : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hf_cont : ContinuousOn (fun x => ‖fderiv ℝ w x‖ ^ 2) (closure Ω) :=
    (ContinuousOn.norm hcont_fderiv).pow 2
  exact (hf_cont.integrableOn_compact hK).mono_set subset_closure

/-- A $C^1$ function on an open set has continuous Fréchet derivative on that set. -/
theorem fderiv_continuousOn_of_contDiffOn {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩo : IsOpen Ω)
    (hw_c1 : ContDiffOn ℝ 1 w Ω) :
    ContinuousOn (fun x => fderiv ℝ w x) Ω :=
  hw_c1.continuousOn_fderiv_of_isOpen hΩo le_rfl

/-- If a $C^1$ function $w$ on a bounded open set $\Omega$ has vanishing Dirichlet energy
$\int_\Omega \|\nabla w\|^2 = 0$, then $\nabla w = 0$ pointwise on $\Omega$. -/
theorem grad_zero_of_gradNormSquaredIntegral_zero {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩo : IsOpen Ω)
    (_hw_diff : DifferentiableOn ℝ w Ω)
    (hw_c1 : ContDiffOn ℝ 1 w Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω))
    (hw : gradNormSquaredIntegral w Ω = 0) :
    ∀ x ∈ Ω, fderiv ℝ w x = 0 := by

  set g : (Fin n → ℝ) → ℝ := fun x => ‖fderiv ℝ w x‖ ^ 2 with hg_def

  have hg_int := gradNormSquared_integrableOn w Ω hΩo hΩb hcont_fderiv
  have hfderiv_cont := fderiv_continuousOn_of_contDiffOn w Ω hΩo hw_c1

  have hg_cont : ContinuousOn g Ω := (ContinuousOn.norm hfderiv_cont).pow 2

  have hg_nonneg_ae : (0 : (Fin n → ℝ) → ℝ) ≤ᵐ[MeasureTheory.MeasureSpace.volume.restrict Ω] g := by
    rw [Filter.EventuallyLE, ae_restrict_iff' hΩo.measurableSet]
    exact ae_of_all _ (fun x _ => by positivity)
  have hg_ae : g =ᵐ[MeasureTheory.MeasureSpace.volume.restrict Ω] 0 := by
    rwa [← setIntegral_eq_zero_iff_of_nonneg_ae hg_nonneg_ae hg_int]

  have hg_zero : Set.EqOn g (fun _ => (0 : ℝ)) Ω :=
    Measure.eqOn_open_of_ae_eq hg_ae hΩo hg_cont continuousOn_const

  intro x hx
  have h := hg_zero hx
  simp [hg_def] at h
  exact h

/-- If $w$ has zero Dirichlet energy on a connected, bounded open set $\Omega$ and is
continuous up to the boundary, then $w$ is constant on $\overline{\Omega}$. -/
theorem gradNormSquared_zero_implies_constant {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hw_diff : DifferentiableOn ℝ w Ω)
    (hw_c1 : ContDiffOn ℝ 1 w Ω)
    (hw_cont : ContinuousOn w (closure Ω))
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω))
    (hw : gradNormSquaredIntegral w Ω = 0) :
    ∃ c : ℝ, ∀ x ∈ closure Ω, w x = c := by

  have h_fderiv_zero : Set.EqOn (fderiv ℝ w) 0 Ω :=
    fun x hx => grad_zero_of_gradNormSquaredIntegral_zero w Ω hΩo hw_diff hw_c1 hΩb hcont_fderiv hw x hx


  obtain ⟨c, hc_Ω⟩ := hΩo.exists_is_const_of_fderiv_eq_zero hΩc.isPreconnected hw_diff h_fderiv_zero

  have hc_closure : Set.EqOn w (fun _ => c) (closure Ω) :=
    Set.EqOn.of_subset_closure
      (fun x hx => hc_Ω x hx)
      hw_cont
      continuousOn_const
      subset_closure
      le_rfl
  exact ⟨c, fun x hx => hc_closure hx⟩

/-- For $n \geq 1$, the whole space $\mathbb{R}^n$ (modeled as `Fin n → ℝ`) is not bounded. -/
lemma not_isBounded_univ_fin_real {n : ℕ} (hn : 0 < n) :
    ¬ Bornology.IsBounded (Set.univ : Set (Fin n → ℝ)) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  push Not
  intro r
  let i₀ : Fin n := ⟨0, hn⟩
  let x : Fin n → ℝ := Function.update 0 i₀ (|r| + 1)
  intro h
  have hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) r := h (Set.mem_univ x)
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have h1 : ‖x i₀‖ ≤ ‖x‖ := norm_le_pi_norm x i₀
  have h2 : x i₀ = |r| + 1 := by simp [x, Function.update_self]
  have h3 : ‖x i₀‖ = |r| + 1 := by rw [h2]; simp; linarith [abs_nonneg r]
  have h4 : |r| + 1 ≤ r := by linarith
  linarith [abs_nonneg r, le_abs_self r]

/-- A nonempty, bounded, open, connected subset of $\mathbb{R}^n$ (with $n \geq 1$) has
nonempty topological boundary. -/
theorem frontier_nonempty_of_bounded_open_connected {n : ℕ}
    (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (_hΩo : IsOpen Ω) (_hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) :
    (frontier Ω).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h

  have hclopen : IsClopen Ω := isClopen_iff_frontier_eq_empty.mpr h

  have hΩ_univ : Ω = Set.univ := hclopen.eq_univ hΩne
  rw [hΩ_univ] at hΩb

  exact absurd hΩb (not_isBounded_univ_fin_real hn)

/-- Linearity of the normal derivative under subtraction:
$\partial_\nu(u - v)(x) = \partial_\nu u(x) - \partial_\nu v(x)$. -/
theorem normalDerivative_sub {n : ℕ} (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    NormalDerivative n (fun y => u y - v y) x =
      NormalDerivative n u x - NormalDerivative n v x := by
  simp only [NormalDerivative]
  have h : (fun y => u y - v y) = u - v := rfl
  rw [h, fderiv_sub hu hv]
  rfl

/-- Glue lemma: a function differentiable at every point of $\overline{\Omega}$ is differentiable
at any particular point of $\overline{\Omega}$. -/
theorem differentiableAt_of_contDiffOn_closure {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω) (_hu_reg : ContDiffOn ℝ 2 u Ω)
    (_hu_cont : ContinuousOn u (closure Ω))
    (hu_diff_closure : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
    (x : Fin n → ℝ) (hx : x ∈ closure Ω) :
    DifferentiableAt ℝ u x :=
  hu_diff_closure x hx

/-- If $\nabla w = 0$ on an open set $\Omega$ and $\nabla w$ is continuous on $\overline{\Omega}$,
then $\nabla w = 0$ extends to the boundary $\partial \Omega$. -/
theorem fderiv_zero_on_frontier_of_zero_on_open {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω)
    (h_zero : ∀ y ∈ Ω, fderiv ℝ w y = 0)
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ frontier Ω) :
    fderiv ℝ w x = 0 := by
  have hx_cl : x ∈ closure Ω := frontier_subset_closure hx
  have h_eq : Set.EqOn (fun x => fderiv ℝ w x) (fun _ => 0) (closure Ω) :=
    Set.EqOn.of_subset_closure h_zero hcont_fderiv continuousOn_const subset_closure le_rfl
  exact h_eq hx_cl

/-- If $w$ has vanishing Dirichlet energy on $\Omega$, then the normal derivative
$\partial_\nu w$ vanishes on $\partial \Omega$. -/
theorem gradNormSquared_zero_implies_normalDerivative_zero {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hw_diff : DifferentiableOn ℝ w Ω)
    (hw_c1 : ContDiffOn ℝ 1 w Ω)
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω))
    (hw : gradNormSquaredIntegral w Ω = 0)
    (x : Fin n → ℝ) (hx : x ∈ frontier Ω) :
    NormalDerivative n w x = 0 := by

  have h_fderiv_zero : ∀ y ∈ Ω, fderiv ℝ w y = 0 :=
    grad_zero_of_gradNormSquaredIntegral_zero w Ω hΩo hw_diff hw_c1 hΩb hcont_fderiv hw

  have h_fderiv_frontier : fderiv ℝ w x = 0 :=
    fderiv_zero_on_frontier_of_zero_on_open w Ω hΩo h_fderiv_zero hcont_fderiv x hx

  simp [NormalDerivative, h_fderiv_frontier]

/-- Under a homogeneous Robin boundary condition $\partial_\nu w + \alpha w = 0$ with $\alpha > 0$,
the boundary energy integral $\int_{\partial \Omega} w \, \partial_\nu w \, dS$ is nonpositive. -/
theorem boundary_energy_nonpos_robin {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
    {α : ℝ} (hα : 0 < α)
    (hbc : ∀ x ∈ frontier Ω, NormalDerivative n w x + α * w x = 0) :
    boundaryEnergyIntegral w Ω ≤ 0 := by
  simp only [boundaryEnergyIntegral]
  have h_eq : Set.EqOn (fun x => w x * NormalDerivative n w x)
      (fun x => -(α * (w x) ^ 2)) (frontier Ω) := by
    intro x hx
    simp only
    have hnd : NormalDerivative n w x = -(α * w x) := by linarith [hbc x hx]
    rw [hnd]; ring
  rw [setIntegral_congr_fun measurableSet_frontier h_eq]
  apply setIntegral_nonpos measurableSet_frontier
  intro x _
  nlinarith [sq_nonneg (w x)]

/-- Under a homogeneous Neumann boundary condition $\partial_\nu w = 0$, the boundary energy
integral vanishes. -/
theorem boundary_energy_zero_neumann {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
    (hbc : ∀ x ∈ frontier Ω, NormalDerivative n w x = 0) :
    boundaryEnergyIntegral w Ω = 0 := by
  simp only [boundaryEnergyIntegral]
  have h : Set.EqOn (fun x => w x * NormalDerivative n w x) (fun _ => (0 : ℝ)) (frontier Ω) :=
    fun x hx => by simp [hbc x hx]
  rw [setIntegral_congr_fun measurableSet_frontier h, setIntegral_const, smul_zero]

/-- Under mixed boundary conditions — $w = 0$ on a Dirichlet portion $S_D$ and $\partial_\nu w = 0$
on a Neumann portion $S_N$, with $\partial \Omega = S_D \cup S_N$ — the boundary energy integral
vanishes. -/
theorem boundary_energy_zero_mixed {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
    {S_D S_N : Set (Fin n → ℝ)}
    (hcover : frontier Ω = S_D ∪ S_N)
    (_hdisjoint : Disjoint S_D S_N)
    (hbc_D : ∀ x ∈ S_D, w x = 0)
    (hbc_N : ∀ x ∈ S_N, NormalDerivative n w x = 0) :
    boundaryEnergyIntegral w Ω = 0 := by
  simp only [boundaryEnergyIntegral]
  have h : Set.EqOn (fun x => w x * NormalDerivative n w x) (fun _ => (0 : ℝ)) (frontier Ω) := by
    intro x hx
    rw [hcover] at hx
    rcases hx with hx | hx
    · simp [hbc_D x hx]
    · simp [hbc_N x hx]
  rw [setIntegral_congr_fun measurableSet_frontier h, setIntegral_const, smul_zero]

/-- Uniqueness for Poisson's equation with Robin boundary conditions $\partial_\nu u + \alpha u = g$
($\alpha > 0$): two solutions $u, v$ of $\Delta u = f = \Delta v$ on a bounded connected open set
$\Omega$ that satisfy the same Robin condition agree on $\overline{\Omega}$. -/
theorem poisson_uniqueness_robin {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {f : (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ}
    {α : ℝ} (hα : 0 < α)
    {u v : (Fin n → ℝ) → ℝ}
    (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
    (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
    (_hu_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
    (_hv_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ v x)
    (_hu_fderiv_cont : ContinuousOn (fun x => fderiv ℝ u x) (closure Ω))
    (_hv_fderiv_cont : ContinuousOn (fun x => fderiv ℝ v x) (closure Ω))
    (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
    (hbc_u : ∀ x ∈ frontier Ω, NormalDerivative n u x + α * u x = g x)
    (hbc_v : ∀ x ∈ frontier Ω, NormalDerivative n v x + α * v x = g x) :
    ∀ x ∈ closure Ω, u x = v x := by

  set w := fun x => u x - v x

  have hw_harmonic : ∀ x ∈ Ω, Laplacian n w x = 0 := by
    intro x hx
    rw [laplacian_sub hΩo _hu_reg _hv_reg hx, hu x hx, hv x hx, sub_self]

  have hw_robin : ∀ x ∈ frontier Ω, NormalDerivative n w x + α * w x = 0 := by
    intro x hx; simp only [w]; rw [normalDerivative_sub u v x (differentiableAt_of_contDiffOn_closure u Ω hΩo _hu_reg _hu_cont _hu_diff_cl x (frontier_subset_closure hx)) (differentiableAt_of_contDiffOn_closure v Ω hΩo _hv_reg _hv_cont _hv_diff_cl x (frontier_subset_closure hx))]; linarith [hbc_u x hx, hbc_v x hx]

  have h_integral_zero : (∫ x in Ω, w x * Laplacian n w x) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx; rw [hw_harmonic x hx, mul_zero]
  have h_energy := energy_identity w Ω hΩo hΩb
  rw [h_integral_zero] at h_energy

  have h_bdy_nonpos := boundary_energy_nonpos_robin w Ω hΩo hΩb hα hw_robin

  have h_grad_nonneg := gradNormSquaredIntegral_nonneg w Ω
  have h_grad_zero : gradNormSquaredIntegral w Ω = 0 := by linarith

  have hw_diff : DifferentiableOn ℝ w Ω :=
    DifferentiableOn.sub (_hu_reg.differentiableOn (by norm_num)) (_hv_reg.differentiableOn (by norm_num))
  have hw_c1 : ContDiffOn ℝ 1 w Ω :=
    (_hu_reg.of_le (by norm_num)).sub (_hv_reg.of_le (by norm_num))
  have hw_cont : ContinuousOn w (closure Ω) := ContinuousOn.sub _hu_cont _hv_cont
  have hw_fderiv_cont : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω) := by
    have heq : Set.EqOn (fun x => fderiv ℝ w x) (fun x => fderiv ℝ u x - fderiv ℝ v x) (closure Ω) := by
      intro x hx
      exact fderiv_sub (_hu_diff_cl x hx) (_hv_diff_cl x hx)
    exact (_hu_fderiv_cont.sub _hv_fderiv_cont).congr heq
  obtain ⟨c, hc⟩ := gradNormSquared_zero_implies_constant w Ω hΩo hΩc hΩb hw_diff hw_c1 hw_cont hw_fderiv_cont h_grad_zero


  have h_nd_zero : ∀ x ∈ frontier Ω, NormalDerivative n w x = 0 :=
    fun x hx => gradNormSquared_zero_implies_normalDerivative_zero w Ω hΩo hΩb hw_diff hw_c1 hw_fderiv_cont h_grad_zero x hx


  have hc_zero : c = 0 := by
    obtain ⟨σ, hσ⟩ := frontier_nonempty_of_bounded_open_connected hn hΩo hΩc hΩb hΩc.nonempty
    have h1 := hw_robin σ hσ; have h2 := h_nd_zero σ hσ; have h3 := hc σ (frontier_subset_closure hσ)
    rw [h2, zero_add] at h1; rw [h3] at h1
    rcases mul_eq_zero.mp h1 with hαz | hcz
    · linarith
    · exact hcz

  intro x hx; have := hc x hx; simp [w] at this ⊢; linarith

/-- Uniqueness up to constants for Poisson's equation with Neumann boundary conditions
$\partial_\nu u = h$: any two solutions $u, v$ differ by an additive constant on $\overline{\Omega}$. -/
theorem poisson_uniqueness_neumann {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {f : (Fin n → ℝ) → ℝ} {h : (Fin n → ℝ) → ℝ}
    {u v : (Fin n → ℝ) → ℝ}
    (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
    (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
    (_hu_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
    (_hv_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ v x)
    (_hu_fderiv_cont : ContinuousOn (fun x => fderiv ℝ u x) (closure Ω))
    (_hv_fderiv_cont : ContinuousOn (fun x => fderiv ℝ v x) (closure Ω))
    (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
    (hbc_u : ∀ x ∈ frontier Ω, NormalDerivative n u x = h x)
    (hbc_v : ∀ x ∈ frontier Ω, NormalDerivative n v x = h x) :
    ∃ c : ℝ, ∀ x ∈ closure Ω, u x = v x + c := by

  set w := fun x => u x - v x

  have hw_harmonic : ∀ x ∈ Ω, Laplacian n w x = 0 := by
    intro x hx
    rw [laplacian_sub hΩo _hu_reg _hv_reg hx, hu x hx, hv x hx, sub_self]

  have hw_neumann : ∀ x ∈ frontier Ω, NormalDerivative n w x = 0 := by
    intro x hx; have h1 := normalDerivative_sub u v x (differentiableAt_of_contDiffOn_closure u Ω hΩo _hu_reg _hu_cont _hu_diff_cl x (frontier_subset_closure hx)) (differentiableAt_of_contDiffOn_closure v Ω hΩo _hv_reg _hv_cont _hv_diff_cl x (frontier_subset_closure hx)); simp only at h1
    rw [h1, hbc_u x hx, hbc_v x hx, sub_self]

  have h_integral_zero : (∫ x in Ω, w x * Laplacian n w x) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx; rw [hw_harmonic x hx, mul_zero]
  have h_energy := energy_identity w Ω hΩo hΩb
  rw [h_integral_zero] at h_energy

  have h_bdy_zero := boundary_energy_zero_neumann w Ω hΩo hΩb hw_neumann
  rw [h_bdy_zero] at h_energy

  have h_grad_zero : gradNormSquaredIntegral w Ω = 0 := by linarith

  have hw_diff : DifferentiableOn ℝ w Ω :=
    DifferentiableOn.sub (_hu_reg.differentiableOn (by norm_num)) (_hv_reg.differentiableOn (by norm_num))
  have hw_c1 : ContDiffOn ℝ 1 w Ω :=
    (_hu_reg.of_le (by norm_num)).sub (_hv_reg.of_le (by norm_num))
  have hw_cont : ContinuousOn w (closure Ω) := ContinuousOn.sub _hu_cont _hv_cont
  have hw_fderiv_cont : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω) := by
    have heq : Set.EqOn (fun x => fderiv ℝ w x) (fun x => fderiv ℝ u x - fderiv ℝ v x) (closure Ω) := by
      intro x hx
      exact fderiv_sub (_hu_diff_cl x hx) (_hv_diff_cl x hx)
    exact (_hu_fderiv_cont.sub _hv_fderiv_cont).congr heq
  obtain ⟨c, hc⟩ := gradNormSquared_zero_implies_constant w Ω hΩo hΩc hΩb hw_diff hw_c1 hw_cont hw_fderiv_cont h_grad_zero


  exact ⟨c, fun x hx => by have := hc x hx; simp [w] at this; linarith⟩

/-- Uniqueness for Poisson's equation under mixed Dirichlet/Neumann boundary conditions: with
$\partial \Omega = S_D \sqcup S_N$ (nonempty Dirichlet portion $S_D$), $u = g_D$ on $S_D$ and
$\partial_\nu u = g_N$ on $S_N$, any two such solutions agree on $\overline{\Omega}$. -/
theorem poisson_uniqueness_mixed {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {f : (Fin n → ℝ) → ℝ}
    {S_D S_N : Set (Fin n → ℝ)}
    (hcover : frontier Ω = S_D ∪ S_N)
    (hdisjoint : Disjoint S_D S_N)
    (hSD_nonempty : S_D.Nonempty)
    {g_D : (Fin n → ℝ) → ℝ} {g_N : (Fin n → ℝ) → ℝ}
    {u v : (Fin n → ℝ) → ℝ}
    (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
    (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
    (_hu_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
    (_hv_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ v x)
    (_hu_fderiv_cont : ContinuousOn (fun x => fderiv ℝ u x) (closure Ω))
    (_hv_fderiv_cont : ContinuousOn (fun x => fderiv ℝ v x) (closure Ω))
    (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
    (hbc_u_D : ∀ x ∈ S_D, u x = g_D x) (hbc_v_D : ∀ x ∈ S_D, v x = g_D x)
    (hbc_u_N : ∀ x ∈ S_N, NormalDerivative n u x = g_N x)
    (hbc_v_N : ∀ x ∈ S_N, NormalDerivative n v x = g_N x) :
    ∀ x ∈ closure Ω, u x = v x := by

  set w := fun x => u x - v x

  have hw_harmonic : ∀ x ∈ Ω, Laplacian n w x = 0 := by
    intro x hx
    rw [laplacian_sub hΩo _hu_reg _hv_reg hx, hu x hx, hv x hx, sub_self]

  have hw_D : ∀ x ∈ S_D, w x = 0 := by
    intro x hx; simp [w, hbc_u_D x hx, hbc_v_D x hx]

  have hw_N : ∀ x ∈ S_N, NormalDerivative n w x = 0 := by
    intro x hx
    have hx_cl : x ∈ closure Ω := frontier_subset_closure (hcover ▸ Set.mem_union_right S_D hx)
    have h1 := normalDerivative_sub u v x (differentiableAt_of_contDiffOn_closure u Ω hΩo _hu_reg _hu_cont _hu_diff_cl x hx_cl) (differentiableAt_of_contDiffOn_closure v Ω hΩo _hv_reg _hv_cont _hv_diff_cl x hx_cl); simp only at h1
    rw [h1, hbc_u_N x hx, hbc_v_N x hx, sub_self]

  have h_integral_zero : (∫ x in Ω, w x * Laplacian n w x) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx; rw [hw_harmonic x hx, mul_zero]
  have h_energy := energy_identity w Ω hΩo hΩb
  rw [h_integral_zero] at h_energy

  have h_bdy_zero := boundary_energy_zero_mixed w Ω hΩo hΩb hcover hdisjoint hw_D hw_N
  rw [h_bdy_zero] at h_energy

  have h_grad_zero : gradNormSquaredIntegral w Ω = 0 := by linarith

  have hw_diff : DifferentiableOn ℝ w Ω :=
    DifferentiableOn.sub (_hu_reg.differentiableOn (by norm_num)) (_hv_reg.differentiableOn (by norm_num))
  have hw_c1 : ContDiffOn ℝ 1 w Ω :=
    (_hu_reg.of_le (by norm_num)).sub (_hv_reg.of_le (by norm_num))
  have hw_cont : ContinuousOn w (closure Ω) := ContinuousOn.sub _hu_cont _hv_cont
  have hw_fderiv_cont : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω) := by
    have heq : Set.EqOn (fun x => fderiv ℝ w x) (fun x => fderiv ℝ u x - fderiv ℝ v x) (closure Ω) := by
      intro x hx
      exact fderiv_sub (_hu_diff_cl x hx) (_hv_diff_cl x hx)
    exact (_hu_fderiv_cont.sub _hv_fderiv_cont).congr heq
  obtain ⟨c, hc⟩ := gradNormSquared_zero_implies_constant w Ω hΩo hΩc hΩb hw_diff hw_c1 hw_cont hw_fderiv_cont h_grad_zero


  have hc_zero : c = 0 := by
    obtain ⟨σ, hσ⟩ := hSD_nonempty
    have h1 := hc σ (frontier_subset_closure (hcover ▸ Set.mem_union_left S_N hσ))
    have h2 := hw_D σ hσ
    linarith

  intro x hx; have := hc x hx; simp [w] at this ⊢; linarith

/-- The spherical mean of $u$ around the point $x$ at radius $r$: the average value of $u$ over
the sphere of radius $r$ centered at $x$, taken with respect to the $(n-1)$-dimensional Hausdorff
measure. By convention, the value at $r = 0$ is $u(x)$. -/
noncomputable def sphericalMean {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then u x
  else ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
    u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- The "spherical-average" function $r \mapsto \fint_{S^{n-1}} u(x + r\omega) \, d\sigma(\omega)$,
i.e. `sphericalMean u x r` but without the special-case branch at $r = 0$. -/
noncomputable def sphericalAvgFun {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ → ℝ :=
  fun r => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
    u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- For a harmonic function $u$ on the ball $B(x, R)$, the spherical average function
$r \mapsto \fint_{S^{n-1}} u(x + r\omega)\, d\sigma(\omega)$ is differentiable on $(0, R)$. -/
theorem sphericalAvgFun_differentiableOn_Ioo {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    DifferentiableOn ℝ (sphericalAvgFun u x) (Set.Ioo 0 R) := by
  have huc := hu.contDiffOn
  set μ := (Measure.hausdorffMeasure (↑(n - 1) : ℝ) : Measure (Fin n → ℝ))
  by_cases hfin : μ (Metric.sphere (0 : Fin n → ℝ) 1) = ⊤
  ·
    have heq : sphericalAvgFun u x = fun _ => 0 := by
      ext r
      show ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, u (x + r • ω) ∂μ = 0
      rw [setAverage_eq]
      have : (μ.real (Metric.sphere (0 : Fin n → ℝ) 1)) = 0 := by
        simp [Measure.real, hfin]
      rw [this, inv_zero, zero_smul]
    rw [heq]; exact differentiableOn_const 0
  ·
    have hfin' : μ (Metric.sphere (0 : Fin n → ℝ) 1) < ⊤ := lt_top_iff_ne_top.mpr hfin
    set ν := μ.restrict (Metric.sphere (0 : Fin n → ℝ) 1)
    haveI hν_fin : IsFiniteMeasure ν := ⟨by rwa [Measure.restrict_apply_univ]⟩
    set c : ℝ := (μ.real (Metric.sphere (0 : Fin n → ℝ) 1))⁻¹
    have heq_fn : sphericalAvgFun u x = c • (fun r => ∫ ω, u (x + r • ω) ∂ν) := by
      ext r; exact setAverage_eq μ _ _
    rw [heq_fn]
    apply DifferentiableOn.const_smul
    intro r₀ hr₀
    apply DifferentiableAt.differentiableWithinAt
    apply HasDerivAt.differentiableAt
    set s := Set.Ioo (r₀ / 2) ((r₀ + R) / 2)
    have hs_nhds : s ∈ nhds r₀ := isOpen_Ioo.mem_nhds
      ⟨by linarith [hr₀.1], by linarith [hr₀.2]⟩
    have hs_pos : ∀ r ∈ s, 0 < r := fun r hr => by linarith [hr.1, hr₀.1]
    have hs_lt_R : ∀ r ∈ s, r < R := fun r hr => by linarith [hr.2, hr₀.2]
    have hmem_ball : ∀ r ∈ s, ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1,
        x + r • ω ∈ Metric.ball x R := by
      intro r hr ω hω
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (hs_pos r hr).le]
      have hω1 : ‖ω‖ = 1 := by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hω
      rw [hω1, mul_one]; exact hs_lt_R r hr
    have hu_diff_at : ∀ r ∈ s, ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1,
        DifferentiableAt ℝ u (x + r • ω) := by
      intro r hr ω hω
      exact (huc.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_ball.mem_nhds (hmem_ball r hr ω hω))
    have hF_cont : ∀ r ∈ s, ContinuousOn (fun ω => u (x + r • ω))
        (Metric.sphere (0 : Fin n → ℝ) 1) := by
      intro r hr
      exact huc.continuousOn.comp
        ((continuous_const.add (continuous_const.smul continuous_id)).continuousOn)
        (fun ω hω => hmem_ball r hr ω hω)


    set K := Metric.closedBall x ((r₀ + R) / 2)
    have hK_compact : IsCompact K := isCompact_closedBall x _
    have hK_sub : K ⊆ Metric.ball x R :=
      Metric.closedBall_subset_ball (by linarith [hr₀.2])

    have hfderiv_cont : ContinuousOn (fderiv ℝ u) (Metric.ball x R) := by
      exact ((contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).mp
        (show ContDiffOn ℝ (1 + 1) u (Metric.ball x R) from by exact_mod_cast huc)).2.2.continuousOn

    have hbdd_fderiv : ∃ M : ℝ, ∀ y ∈ K, ‖fderiv ℝ u y‖ ≤ M := by
      have := hK_compact.bddAbove_image (hfderiv_cont.norm.mono hK_sub)
      obtain ⟨M, hM⟩ := this
      exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
    obtain ⟨M, hM⟩ := hbdd_fderiv

    have hr₀s : r₀ ∈ s := ⟨by linarith [hr₀.1], by linarith [hr₀.2]⟩

    have hν_eq : ν.restrict (Metric.sphere (0 : Fin n → ℝ) 1) = ν :=
      Measure.restrict_restrict_of_subset (fun _ h => h)

    have norm_of_mem_sphere : ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1, ‖ω‖ = 1 :=
      fun ω hω => by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hω


    set_option maxHeartbeats 400000 in
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
      (F := fun r ω => u (x + r • ω))
      (F' := fun r ω => fderiv ℝ u (x + r • ω) ω)
      (bound := fun _ => M + 1)
      hs_nhds ?_ ?_ ?_ ?_ ?_ ?_).2

    · filter_upwards [hs_nhds] with r hr
      exact (hF_cont r hr).aestronglyMeasurable isClosed_sphere.measurableSet

    · have hint : IntegrableOn (fun ω => u (x + r₀ • ω))
          (Metric.sphere (0 : Fin n → ℝ) 1) ν :=
        (hF_cont r₀ hr₀s).integrableOn_compact (μ := ν) (isCompact_sphere _ _)
      exact hν_eq ▸ hint

    · have : ContinuousOn (fun ω => fderiv ℝ u (x + r₀ • ω) ω)
          (Metric.sphere (0 : Fin n → ℝ) 1) := by
        intro ω hω
        apply ContinuousWithinAt.clm_apply
        · exact (hfderiv_cont.comp
            ((continuous_const.add (continuous_const.smul continuous_id)).continuousOn)
            (fun ω' hω' => hmem_ball r₀ hr₀s ω' hω')).continuousWithinAt hω
        · exact continuousWithinAt_id
      exact this.aestronglyMeasurable isClosed_sphere.measurableSet

    · apply ae_restrict_of_forall_mem isClosed_sphere.measurableSet
      intro ω hω r hr
      dsimp only
      have hω1 := norm_of_mem_sphere ω hω
      have hpt : x + r • ω ∈ K := by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg (hs_pos r hr).le, hω1, mul_one]
        linarith [hr.2]
      calc ‖fderiv ℝ u (x + r • ω) ω‖
          ≤ ‖fderiv ℝ u (x + r • ω)‖ * ‖ω‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * 1 := by
            rw [hω1]
            exact mul_le_mul_of_nonneg_right (hM _ hpt) zero_le_one
        _ ≤ M + 1 := by linarith

    · exact integrable_const _

    · apply ae_restrict_of_forall_mem isClosed_sphere.measurableSet
      intro ω hω r hr
      dsimp only
      have hu_da := hu_diff_at r hr ω hω
      have h_aff : HasDerivAt (fun t => x + t • ω) ω r := by
        have h1 : HasDerivAt (fun t => t • ω) ((1 : ℝ) • ω) r :=
          (hasDerivAt_id' r).smul_const ω
        have h2 : HasDerivAt (fun _ => x) 0 r := hasDerivAt_const r x
        have h3 := h2.add h1
        simp only [one_smul, zero_add] at h3; exact h3
      exact hu_da.hasFDerivAt.comp_hasDerivAt r h_aff


/-- The divergence theorem applied to $\nabla u$ on the ball $B(x, r)$:
$\int_{B(x,r)} \Delta u = \int_{\partial B(x,r)} \partial_\nu u \, dS$. -/
theorem divergence_theorem_ball {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hu : ContDiffOn ℝ 2 u (Metric.closedBall x r)) :
    ∫ y in Metric.ball x r, Laplacian n u y =
      ∫ y in frontier (Metric.ball x r), NormalDerivative n u y ∂(surfaceMeasure n (Metric.ball x r)) := by sorry


/-- For a $C^2$ function $u$ on $B(x, R)$, the derivative of the spherical average function at
$r \in (0, R)$ is, up to a constant $K$, the boundary integral of the normal derivative
$\int_{\partial B(x,r)} \partial_\nu u \, dS$. -/
theorem sphericalAvgFun_deriv_eq_boundary_normal_integral {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : ContDiffOn ℝ 2 u (Metric.ball x R))
    (r : ℝ) (hr : r ∈ Set.Ioo 0 R) :
    ∃ (K : ℝ), deriv (sphericalAvgFun u x) r = K *
      ∫ y in frontier (Metric.ball x r), NormalDerivative n u y ∂(surfaceMeasure n (Metric.ball x r)) := by sorry


/-- Combining the boundary-normal formula for the derivative of the spherical mean with the
divergence theorem: for $r \in (0, R)$, the derivative of the spherical-average function is, up
to a constant, the volume integral of the Laplacian, $C \cdot \int_{B(x,r)} \Delta u$. -/
theorem sphericalAvgFun_deriv_eq_scaled_laplacian_integral {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : ContDiffOn ℝ 2 u (Metric.ball x R))
    (r : ℝ) (hr : r ∈ Set.Ioo 0 R) :
    ∃ (C : ℝ), deriv (sphericalAvgFun u x) r = C * ∫ y in Metric.ball x r, Laplacian n u y := by

  obtain ⟨K, hK⟩ := sphericalAvgFun_deriv_eq_boundary_normal_integral u x R hR hu r hr

  have hr_pos : 0 < r := hr.1
  have hr_lt : r < R := hr.2
  have hu_closed : ContDiffOn ℝ 2 u (Metric.closedBall x r) :=
    hu.mono (Metric.closedBall_subset_ball hr_lt)
  have hdiv := divergence_theorem_ball u x r hr_pos hu_closed

  exact ⟨K, by rw [hK, hdiv]⟩

/-- For a harmonic function $u$ on the ball $B(x, R)$, the derivative of the spherical-average
function $r \mapsto \fint_{S^{n-1}} u(x + r\omega)$ vanishes on $(0, R)$. -/
theorem sphericalAvgFun_deriv_eq_zero_of_harmonic {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    (Set.Ioo 0 R).EqOn (deriv (sphericalAvgFun u x)) 0 := by
  intro r hr
  simp only [Pi.zero_apply]
  obtain ⟨C, hC⟩ := sphericalAvgFun_deriv_eq_scaled_laplacian_integral u x R hR
    hu.contDiffOn r hr
  rw [hC]
  suffices h : ∫ y in Metric.ball x r, Laplacian n u y = 0 by
    rw [h, mul_zero]
  have h_sub : Metric.ball x r ⊆ Metric.ball x R :=
    Metric.ball_subset_ball (le_of_lt hr.2)
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  exact hu.laplacian_eq_zero y (h_sub hy)

/-- If $u$ is continuous at $x$, then for any $t$ the scaled translate $\omega \mapsto u(x + t\omega)$
is integrable over the unit sphere with respect to the $(n-1)$-Hausdorff measure. -/
theorem integrableOn_sphere_of_continuousAt (n : ℕ) (hn : 0 < n)
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hu : ContinuousAt u x) (t : ℝ) :
    IntegrableOn (fun ω => u (x + t • ω)) (Metric.sphere (0 : Fin n → ℝ) 1)
      (Measure.hausdorffMeasure (↑(n - 1) : ℝ)) := by sorry


/-- If $\|f(\omega) - c\| \leq C$ uniformly on the unit sphere $S^{n-1}$, then the deviation
of the spherical average from $c$ is also bounded by $C$:
$\|\fint_{S^{n-1}} f \, d\sigma - c\| \leq C$. -/
theorem norm_setAverage_sub_le {n : ℕ} (hn : 0 < n)
    (f : (Fin n → ℝ) → ℝ) (c C : ℝ) (hC : 0 ≤ C)
    (hf_int : IntegrableOn f (Metric.sphere (0 : Fin n → ℝ) 1)
      (Measure.hausdorffMeasure (↑(n - 1) : ℝ)))
    (hbound : ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1, ‖f ω - c‖ ≤ C) :
    ‖(⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, f ω
      ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) - c‖ ≤ C := by sorry


/-- If $u$ is continuous at $x$, then the spherical average $\fint_{S^{n-1}} u(x + t\omega)\,
d\sigma(\omega)$ tends to $u(x)$ as $t \to 0^+$. -/
theorem setAverage_sphere_tendsto_of_continuousAt {n : ℕ} (hn : 0 < n)
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hu : ContinuousAt u x) :
    Tendsto (fun (t : ℝ) => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + t • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.continuousAt_iff] at hu
  obtain ⟨δ, hδ, hδ_bound⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun t ht_pos ht_dist => ?_⟩
  have ht_lt_δ : t < δ := by
    rw [Real.dist_eq, sub_zero] at ht_dist; exact lt_of_abs_lt ht_dist
  have ht_pos' : (0 : ℝ) < t := ht_pos
  have h_bound : ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1,
      ‖u (x + t • ω) - u x‖ ≤ ε / 2 := by
    intro ω hω
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact le_of_lt (hδ_bound (by
      rw [dist_eq_norm, show x + t • ω - x = t • ω from by ring,
          norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos',
          mem_sphere_zero_iff_norm.mp hω, mul_one]
      exact ht_lt_δ))
  have hf_int := integrableOn_sphere_of_continuousAt n hn u x
      (by rwa [Metric.continuousAt_iff]) t
  calc dist (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, u (x + t • ω)
        ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) (u x)
      = ‖(⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, u (x + t • ω)
        ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) - u x‖ := by
          rw [Real.dist_eq, Real.norm_eq_abs]
    _ ≤ ε / 2 := norm_setAverage_sub_le hn _ _ _ (le_of_lt (half_pos hε)) hf_int h_bound
    _ < ε := half_lt_self hε

/-- For $u$ harmonic on $B(x, R)$ and $0 < s \leq r < R$, the spherical averages of $u$ over
spheres of radii $s$ and $r$ centered at $x$ agree. -/
theorem sphericalAvg_const_of_harmonic {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R))
    (r s : ℝ) (hr_pos : 0 < r) (hr_lt : r < R) (hs_pos : 0 < s) (hs_le : s ≤ r) :
    (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + s • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) =
    (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) := by

  show sphericalAvgFun u x s = sphericalAvgFun u x r

  have hs_mem : s ∈ Set.Ioo 0 R := ⟨hs_pos, lt_of_le_of_lt hs_le hr_lt⟩
  have hr_mem : r ∈ Set.Ioo 0 R := ⟨hr_pos, hr_lt⟩


  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (sphericalAvgFun_differentiableOn_Ioo u x R hR hu)
    (sphericalAvgFun_deriv_eq_zero_of_harmonic u x R hR hu)
    hs_mem hr_mem

/-- For $u$ harmonic on $B(x, R)$, the spherical average $\fint_{S^{n-1}} u(x + t\omega)\,
d\sigma(\omega)$ tends to $u(x)$ as $t \to 0^+$ (specialization of the continuity-based version). -/
theorem sphericalAvg_tendsto_at_zero {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    Tendsto (fun (t : ℝ) => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + t • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) := by

  have hx_mem : x ∈ Metric.ball x R := Metric.mem_ball_self hR
  have hu_cont : ContinuousAt u x :=
    hu.contDiffOn.continuousOn.continuousAt (isOpen_ball.mem_nhds hx_mem)
  exact setAverage_sphere_tendsto_of_continuousAt hn u x hu_cont

/-- Spherical mean-value property: for $u$ harmonic on $B(x, R)$ and any $r \in (0, R)$, the
spherical average $\fint_{S^{n-1}} u(x + r\omega)\, d\sigma(\omega)$ equals $u(x)$. -/
theorem sphericalMean_integral_eq_center {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R))
    (r : ℝ) (hr_pos : 0 < r) (hr_lt : r < R) :
    (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) = u x := by

  set val := (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) with hval_def

  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
        u (x + s • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) = val := by
    rw [eventually_nhdsWithin_iff]
    refine Filter.eventually_of_mem (Iio_mem_nhds (show (0 : ℝ) < r from hr_pos))
      (fun s hs hmem => ?_)
    exact sphericalAvg_const_of_harmonic u x R hR hu r s hr_pos hr_lt hmem (le_of_lt hs)

  have h_lim := sphericalAvg_tendsto_at_zero hn u x R hR hu

  exact tendsto_nhds_unique (tendsto_nhds_of_eventually_eq hev) h_lim

/-- For $u$ harmonic on $B(x, R)$, the function $r \mapsto$ `sphericalMean u x r` is constant on
$[0, R)$. -/
theorem sphericalMean_const_on_Ico_of_harmonic {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R))
    (r s : ℝ) (hr : r ∈ Set.Ico (0:ℝ) R) (hs : s ∈ Set.Ico (0:ℝ) R) :
    sphericalMean u x r = sphericalMean u x s := by

  suffices h : ∀ t, t ∈ Set.Ico (0:ℝ) R → sphericalMean u x t = u x from
    (h r hr).trans (h s hs).symm
  intro t ht
  by_cases ht0 : t = 0
  ·
    simp [sphericalMean, ht0]
  ·
    have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    simp only [sphericalMean, ht0, ite_false]
    exact sphericalMean_integral_eq_center hn u x R hR hu t ht_pos ht.2

/-- Since `sphericalMean u x` is constant on $[0, R)$ for harmonic $u$, it has right derivative
zero at any $t \in [0, R)$ (in the sense of `HasDerivWithinAt` restricted to $[t, \infty)$). -/
theorem sphericalMean_hasDerivWithinAt_zero_divergence
    {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (R : ℝ)
    (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R))
    (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) R) :
    HasDerivWithinAt (sphericalMean u x) 0 (Set.Ici t) t := by

  have hlc : ∀ᶠ x_1 in nhdsWithin t (Set.Ici t), sphericalMean u x x_1 = sphericalMean u x t := by
    rw [eventually_nhdsWithin_iff]
    exact Filter.eventually_of_mem (Iio_mem_nhds ht.2) fun x_1 hx1 hmem =>
      sphericalMean_const_on_Ico_of_harmonic hn u x R hR hu x_1 t
        ⟨le_trans ht.1 hmem, hx1⟩ ht

  exact HasDerivWithinAt.congr_of_eventuallyEq
    (hasDerivWithinAt_const t (Set.Ici t) (sphericalMean u x t)) hlc rfl

/-- For $u$ harmonic on $B(x, R)$ and $0 < b < R$, the spherical mean function is continuous on
the closed interval $[0, b]$. -/
theorem sphericalMean_continuousOn_Icc_sub
    {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (R : ℝ)
    (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R))
    (b : ℝ) (_hb_pos : 0 < b) (hb_lt : b < R) :
    ContinuousOn (sphericalMean u x) (Set.Icc 0 b) := by

  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) R := ⟨le_refl 0, hR⟩
  have hf_eq : ∀ r ∈ Set.Icc (0:ℝ) b, sphericalMean u x r = sphericalMean u x 0 := by
    intro r hr
    have hr_ico : r ∈ Set.Ico (0:ℝ) R := ⟨hr.1, lt_of_le_of_lt hr.2 hb_lt⟩
    exact sphericalMean_const_on_Ico_of_harmonic hn u x R hR hu r 0 hr_ico h0
  exact continuousOn_const.congr hf_eq

/-- For $u$ harmonic on $B(x, R)$, the spherical mean function is locally constant from the right
at every $r \in [0, R)$: it agrees with `sphericalMean u x r` on a right-neighborhood of $r$
in $[r, \infty)$. -/
theorem sphericalMean_locallyConst_of_harmonic {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R))
    (r : ℝ) (hr : r ∈ Set.Ico (0:ℝ) R) :
    ∀ᶠ t in nhdsWithin r (Set.Ici r),
      sphericalMean u x t = sphericalMean u x r := by
  rw [eventually_nhdsWithin_iff]
  refine Filter.eventually_of_mem (Iio_mem_nhds hr.2) (fun t ht hmem => ?_)
  have htIco : t ∈ Set.Ico (0:ℝ) R := ⟨le_trans hr.1 hmem, ht⟩
  exact sphericalMean_const_on_Ico_of_harmonic hn u x R hR hu t r htIco hr

/-- The right derivative of the spherical mean function is zero at every $r \in [0, R)$, for $u$
harmonic on $B(x, R)$. -/
theorem sphericalMean_hasDerivWithinAt_zero {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R))
    (r : ℝ) (hr : r ∈ Set.Ico (0:ℝ) R) :
    HasDerivWithinAt (sphericalMean u x) 0 (Set.Ici r) r := by

  have hlc := sphericalMean_locallyConst_of_harmonic hn u x R hR hu r hr

  have hconst : HasDerivWithinAt (fun _ => sphericalMean u x r) 0 (Set.Ici r) r :=
    hasDerivWithinAt_const r (Set.Ici r) (sphericalMean u x r)

  exact hconst.congr_of_eventuallyEq_of_mem hlc (le_refl r)

/-- For $u$ harmonic on $B(x, R)$, the spherical mean function is differentiable on $[0, R)$
(in the sense of `DifferentiableOn`). -/
theorem sphericalMean_diffOn_Ico {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    DifferentiableOn ℝ (sphericalMean u x) (Set.Ico 0 R) := by
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) R := ⟨le_refl 0, hR⟩
  apply DifferentiableOn.congr (differentiableOn_const (sphericalMean u x 0))
  intro r hr
  exact sphericalMean_const_on_Ico_of_harmonic hn u x R hR hu r 0 hr h0


/-- Left-continuity of the spherical-average function at $r = R$ for $u$ harmonic on $B(x, R)$:
the average $\fint_{S^{n-1}} u(x + r\omega)$ tends, as $r \to R^-$, to the corresponding average
at radius $R$. -/
theorem setAverage_sphere_leftContinuousAt {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R)
    (hu : IsHarmonic u (Metric.ball x R)) :
    Filter.Tendsto (fun (r : ℝ) => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ))
    (nhdsWithin R (Set.Iio R)) (nhds (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + R • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ))) := by sorry

/-- The spherical mean-value property extended to the boundary radius: for $u$ harmonic on
$B(x, R)$, $\fint_{S^{n-1}} u(x + R\omega)\, d\sigma(\omega) = u(x)$. -/
theorem sphericalMean_avg_eq_center_at_boundary {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + R • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) = u x := by

  have hg_eq : ∀ r, 0 < r → r < R →
      (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
        u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) = u x :=
    fun r hr hrR => sphericalMean_integral_eq_center hn u x R hR hu r hr hrR

  have h_tendsto_ux : Filter.Tendsto
      (fun r => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
        u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ))
      (nhdsWithin R (Set.Iio R)) (nhds (u x)) := by
    have hev : ∀ᶠ r in nhdsWithin R (Set.Iio R),
        (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
          u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) = u x := by
      rw [eventually_nhdsWithin_iff]
      refine Filter.eventually_of_mem (Ioi_mem_nhds (show R / 2 < R by linarith)) ?_
      intro r hr hmem
      exact hg_eq r (lt_of_lt_of_le (by linarith : (0 : ℝ) < R / 2) (le_of_lt hr)) hmem
    exact tendsto_nhds_of_eventually_eq hev

  have h_tendsto_gR := setAverage_sphere_leftContinuousAt u x R hR hu

  have hne : (nhdsWithin R (Set.Iio R)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hR⟩
  exact tendsto_nhds_unique h_tendsto_gR h_tendsto_ux

/-- For $u$ harmonic on $B(x, R)$, the spherical-average function is continuous within $[0, R]$
at the endpoint $R$. -/
theorem sphericalMean_avg_continuousWithinAt {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    ContinuousWithinAt
      (fun r => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
        u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ))
      (Set.Icc 0 R) R := by

  have hev : ∀ᶠ r in nhdsWithin R (Set.Icc 0 R),
      (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
        u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) = u x := by
    rw [eventually_nhdsWithin_iff]
    refine Filter.eventually_of_mem (Ioi_mem_nhds (show R / 2 < R by linarith)) ?_
    intro r hr hmem
    by_cases hR_eq : r = R
    · rw [hR_eq]; exact sphericalMean_avg_eq_center_at_boundary hn u x R hR hu
    · have hr_lt : r < R := lt_of_le_of_ne hmem.2 hR_eq
      have hr_pos : 0 < r := lt_of_lt_of_le (by linarith : 0 < R / 2) (le_of_lt hr)
      exact sphericalMean_integral_eq_center hn u x R hR hu r hr_pos hr_lt

  exact continuousWithinAt_const.congr_of_eventuallyEq_of_mem hev (right_mem_Icc.mpr (le_of_lt hR))

/-- For $u$ harmonic on $B(x, R)$, the spherical mean function `sphericalMean u x` is continuous
within $[0, R]$ at the endpoint $R$. -/
theorem sphericalMean_continuousWithinAt_endpoint {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    ContinuousWithinAt (sphericalMean u x) (Set.Icc 0 R) R := by

  have hcont := sphericalMean_avg_continuousWithinAt hn u x R hR hu

  apply ContinuousWithinAt.congr_of_eventuallyEq_of_mem hcont _ (right_mem_Icc.mpr (le_of_lt hR))
  rw [eventuallyEq_nhdsWithin_iff]
  refine Filter.eventually_of_mem (Ioi_mem_nhds (by linarith : R / 2 < R)) ?_
  intro r hr hmem
  simp only [sphericalMean]
  have : r ≠ 0 := ne_of_gt (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ R / 2) hr)
  simp [this]

/-- For $u$ harmonic on $B(x, R)$, the spherical mean function is continuous on the closed
interval $[0, R]$. -/
theorem sphericalMean_continuousOn {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    ContinuousOn (sphericalMean u x) (Set.Icc 0 R) := by
  intro r hr
  by_cases hne : r ≠ R
  ·
    have hrR : r < R := lt_of_le_of_ne hr.2 hne
    have hcont_ico : ContinuousOn (sphericalMean u x) (Set.Ico 0 R) :=
      (sphericalMean_diffOn_Ico hn u x R hR hu).continuousOn
    have hcwi : ContinuousWithinAt (sphericalMean u x) (Set.Ico 0 R) r :=
      hcont_ico r ⟨hr.1, hrR⟩


    exact hcwi.mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Set.Iio R, isOpen_Iio, hrR, fun _ ⟨hx1, hx2⟩ => ⟨hx2.1, hx1⟩⟩)
  ·
    simp only [ne_eq, not_not] at hne
    rw [hne]
    exact sphericalMean_continuousWithinAt_endpoint hn u x R hR hu

/-- By definition, `sphericalMean u x 0 = u x`. -/
theorem sphericalMean_at_zero {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (_hR : 0 < R) (_hu : IsHarmonic u (Metric.ball x R)) :
    sphericalMean u x 0 = u x := by
  simp [sphericalMean]

/-- Spherical mean-value property for harmonic functions: for $u$ harmonic on $B(x, R)$ and any
$r \in (0, R]$, the spherical mean satisfies `sphericalMean u x r = u(x)`. -/
theorem harmonic_sphere_mean_value {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (R : ℝ)
    (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    sphericalMean u x r = u x := by

  have h_deriv_g : ∀ t ∈ Set.Ico (0:ℝ) R,
      HasDerivWithinAt (sphericalMean u x) (0:ℝ) (Set.Ici t) t :=
    fun t ht => sphericalMean_hasDerivWithinAt_zero hn u x R hR hu t ht
  have h_deriv_c : ∀ t ∈ Set.Ico (0:ℝ) R,
      HasDerivWithinAt (fun _ => u x) (0:ℝ) (Set.Ici t) t :=
    fun t _ => hasDerivWithinAt_const t (Set.Ici t) (u x)

  have h_cont_g : ContinuousOn (sphericalMean u x) (Set.Icc 0 R) :=
    sphericalMean_continuousOn hn u x R hR hu
  have h_cont_c : ContinuousOn (fun _ : ℝ => u x) (Set.Icc 0 R) := continuousOn_const

  have h_eq_zero : sphericalMean u x 0 = (fun _ : ℝ => u x) 0 := by
    simp [sphericalMean_at_zero u x R hR hu]

  exact eq_of_has_deriv_right_eq h_deriv_g h_deriv_c h_cont_g h_cont_c h_eq_zero
    r ⟨le_of_lt hr, hrR⟩

/-- Polar-coordinate decomposition of a ball integral: for a function $g$ on $\mathbb{R}^n$,
$\int_{B(0,R)} g(y)\, dy = |B(0,1)| \cdot n \int_0^R r^{n-1} \fint_{S^{n-1}} g(r\omega)\, d\omega \, dr$,
where the inner average is taken with respect to the `toSphere` measure on the unit sphere. -/
theorem polar_coordinate_ball_integral_toSphere {n : ℕ} (hn : 0 < n)
    (g : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R) :
    ∫ y in Metric.ball (0 : Fin n → ℝ) R, g y =
      (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal * ↑n *
      ∫ r in (0 : ℝ)..R, r ^ ((↑n : ℝ) - 1) *
        (⨍ ω : Metric.sphere (0 : Fin n → ℝ) 1, g (r • ω.val)
          ∂(volume : Measure (Fin n → ℝ)).toSphere) := by sorry

/-- Compatibility of two spherical averages on $S^{n-1}$: the average computed via the
`toSphere` measure derived from the Lebesgue measure agrees with the average computed via the
$(n-1)$-dimensional Hausdorff measure. -/
theorem average_toSphere_eq_setAverage_hausdorff {n : ℕ} (hn : 0 < n)
    (f : (Fin n → ℝ) → ℝ) :
    ⨍ ω : Metric.sphere (0 : Fin n → ℝ) 1, f ω.val
      ∂(volume : Measure (Fin n → ℝ)).toSphere =
    ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, f ω
      ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ) := by sorry

/-- Polar-coordinate decomposition of a ball integral with the spherical average expressed via
the $(n-1)$-Hausdorff measure:
$\int_{B(0,R)} g(y)\, dy = |B(0,1)| \cdot n \int_0^R r^{n-1} \fint_{S^{n-1}} g(r\omega)\, d\sigma(\omega)\, dr$. -/
theorem setIntegral_ball_zero_eq_radial_sphericalAvg {n : ℕ} (hn : 0 < n)
    (g : (Fin n → ℝ) → ℝ) (R : ℝ) (hR : 0 < R) :
    ∫ y in Metric.ball (0 : Fin n → ℝ) R, g y =
      (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal * ↑n *
      ∫ r in (0 : ℝ)..R, r ^ ((↑n : ℝ) - 1) *
        (⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
          g (r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) := by

  rw [polar_coordinate_ball_integral_toSphere hn g R hR]

  congr 1
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r _
  congr 1
  exact average_toSphere_eq_setAverage_hausdorff hn (fun ω => g (r • ω))

set_option maxHeartbeats 400000 in
/-- Radial decomposition of the integral of $u$ over $B(x, R)$ in terms of spherical means:
$\int_{B(x,R)} u(y)\, dy = |B(0,1)| \cdot n \int_0^R r^{n-1} \cdot \mathrm{sphericalMean}(u, x, r)\, dr$. -/
theorem setIntegral_ball_eq_radial_sphericalMean {n : ℕ} (hn : 0 < n)
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) :
    ∫ y in Metric.ball x R, u y =
      (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal * ↑n *
      ∫ r in (0 : ℝ)..R, r ^ ((↑n : ℝ) - 1) * sphericalMean u x r := by

  have htranslate : ∫ y in Metric.ball x R, u y =
      ∫ y in Metric.ball (0 : Fin n → ℝ) R, u (y + x) := by
    rw [← (measurePreserving_add_right volume x).setIntegral_preimage_emb
          (Homeomorph.addRight x).measurableEmbedding u (Metric.ball x R)]
    congr 1; ext y; simp
  rw [htranslate]
  simp_rw [add_comm _ x]

  rw [setIntegral_ball_zero_eq_radial_sphericalAvg hn (fun y => u (x + y)) R hR]

  congr 1
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r hr
  congr 1
  simp only [sphericalMean]

  have hr_pos : r > 0 := by
    rw [Set.uIoc, min_eq_left hR.le, max_eq_right hR.le] at hr; exact hr.1
  rw [if_neg (ne_of_gt hr_pos)]

/-- Volume average of $u$ over $B(x, R)$ as a weighted integral of spherical means:
$\fint_{B(x,R)} u \, dy = \frac{n}{R^n} \int_0^R r^{n-1} \cdot \mathrm{sphericalMean}(u, x, r)\, dr$. -/
theorem polar_coordinate_volume_decomposition {n : ℕ} (hn : 0 < n) (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) :
    ⨍ y in Metric.ball x R, u y =
      (n / R ^ (n : ℝ)) * ∫ r in (0 : ℝ)..R, r ^ ((n : ℝ) - 1) * sphericalMean u x r := by

  rw [MeasureTheory.setAverage_eq]

  rw [setIntegral_ball_eq_radial_sphericalMean hn u x R hR]

  set I := ∫ r in (0 : ℝ)..R, r ^ ((↑n : ℝ) - 1) * sphericalMean u x r
  set V1 := (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal
  haveI : Nontrivial (Fin n → ℝ) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Function.nontrivial
  have hVR : volume.real (Metric.ball x R) = R ^ n * V1 := by
    simp only [Measure.real, Measure.addHaar_ball volume x hR.le]
    rw [Module.finrank_fin_fun ℝ, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hR.le n)]
  have hV1_ne : V1 ≠ 0 := ne_of_gt
    (ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne)
  have hRn_ne : (R : ℝ) ^ (n : ℕ) ≠ 0 := ne_of_gt (pow_pos hR n)

  rw [hVR, smul_eq_mul]
  have hRpow : R ^ (n : ℝ) = R ^ n := by
    rw [← Real.rpow_natCast R n, Real.rpow_natCast]
  rw [div_mul_eq_mul_div, hRpow]
  field_simp

/-- If the spherical mean `sphericalMean u x r` equals a constant $c$ for every $r \in (0, R]$,
then the volume average of $u$ over $B(x, R)$ equals $c$. -/
theorem volume_average_from_constant_sphere_mean {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (c : ℝ)
    (hsphere : ∀ r : ℝ, 0 < r → r ≤ R → sphericalMean u x r = c)
    (hn : 0 < n) :
    ⨍ y in Metric.ball x R, u y = c := by
  rw [polar_coordinate_volume_decomposition hn u x R hR]

  have hint_eq : ∫ r in (0 : ℝ)..R, r ^ ((n : ℝ) - 1) * sphericalMean u x r =
      ∫ r in (0 : ℝ)..R, r ^ ((n : ℝ) - 1) * c := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro r hr

    show r ^ ((n : ℝ) - 1) * sphericalMean u x r = r ^ ((n : ℝ) - 1) * c
    have : r ∈ Ioc 0 R := by
      rwa [Set.uIoc, min_eq_left hR.le, max_eq_right hR.le] at hr
    congr 1
    exact hsphere r this.1 this.2
  rw [hint_eq]

  simp_rw [mul_comm _ c]
  rw [intervalIntegral.integral_const_mul]

  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [integral_rpow (by left; linarith)]
  have h1 : (n : ℝ) - 1 + 1 = (n : ℝ) := by ring
  rw [h1, Real.zero_rpow (ne_of_gt hn_pos), sub_zero]
  field_simp

/-- Volume mean-value property for harmonic functions: if $u$ is harmonic on $\Omega$ and
$\overline{B(x, R)} \subseteq \Omega$, then $u(x) = \fint_{B(x, R)} u(y)\, dy$. -/
protected theorem harmonic_volume_mean_value {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : IsHarmonic u Ω)
    {x : Fin n → ℝ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x R ⊆ Ω) :
    u x = ⨍ y in Metric.ball x R, u y := by

  have hu_ball : IsHarmonic u (Metric.ball x R) :=
    ⟨hu.contDiffOn.mono (Metric.ball_subset_closedBall.trans hball),
     fun y hy => hu.laplacian_eq_zero y (hball (Metric.ball_subset_closedBall hy))⟩

  have hsphere : ∀ r : ℝ, 0 < r → r ≤ R → sphericalMean u x r = u x :=
    fun r hr hrR => harmonic_sphere_mean_value hn u x R hR hu_ball r hr hrR

  exact (volume_average_from_constant_sphere_mean u x R hR (u x) hsphere hn).symm

/-- The predicate that $u$ is continuous on $\Omega$ and satisfies the volume mean-value property
on $\Omega$: for every $x \in \Omega$ and every closed ball $\overline{B(x, R)} \subseteq \Omega$,
$u(x) = \fint_{B(x, R)} u$. -/
def HasVolumeMVP {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop :=
  ContinuousOn u Ω ∧
  ∀ (x : Fin n → ℝ) (R : ℝ), x ∈ Ω → 0 < R → Metric.closedBall x R ⊆ Ω →
    u x = ⨍ y in Metric.ball x R, u y

/-- Mean-value maximum lemma: if a continuous function $u$ satisfies the volume MVP at $q$ on
$B(q, r)$, is bounded above by $M$ on $B(q, r)$, and attains the value $M$ at $q$, then $u \equiv M$
on the whole open ball $B(q, r)$. -/
theorem mvp_max_const_on_ball {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {q : Fin n → ℝ} {r : ℝ} {M : ℝ}
    (hr : 0 < r) (Ω : Set (Fin n → ℝ))
    (hball : Metric.closedBall q r ⊆ Ω)
    (hcont : ContinuousOn u Ω)
    (hmvp_q : u q = ⨍ y in Metric.ball q r, u y)
    (hle : ∀ y ∈ Metric.ball q r, u y ≤ M)
    (hqM : u q = M) :
    ∀ y ∈ Metric.ball q r, u y = M := by

  have hμ_pos : (volume (Metric.ball q r)) ≠ 0 := (measure_ball_pos volume q hr).ne'
  have hμ_fin : (volume (Metric.ball q r)) ≠ ⊤ := measure_ball_lt_top.ne
  have hreal_pos : (0 : ℝ) < volume.real (Metric.ball q r) :=
    ENNReal.toReal_pos hμ_pos hμ_fin

  have hcont_ball : ContinuousOn u (Metric.closedBall q r) := hcont.mono hball
  have hint_u : IntegrableOn u (Metric.ball q r) volume :=
    (hcont_ball.integrableOn_compact (isCompact_closedBall q r)).mono_set ball_subset_closedBall
  have hint_M : IntegrableOn (fun _ => M) (Metric.ball q r) volume := integrableOn_const

  have hle_ae : u ≤ᶠ[ae (volume.restrict (Metric.ball q r))] (fun _ => M) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hle y hy

  have havg_eq : ⨍ y in Metric.ball q r, u y = M := by linarith [hmvp_q, hqM]

  have hint_eq : ∫ y in Metric.ball q r, u y = ∫ y in Metric.ball q r, (fun _ => M) y := by
    rw [setAverage_eq] at havg_eq
    simp only [setIntegral_const, smul_eq_mul]
    have h := havg_eq
    rw [smul_eq_mul] at h
    field_simp at h ⊢
    linarith

  have hae_eq : u =ᶠ[ae (volume.restrict (Metric.ball q r))] (fun _ => M) := by
    exact (integral_eq_iff_of_ae_le hint_u hint_M hle_ae).mp hint_eq

  have hcont_u_ball : ContinuousOn u (Metric.ball q r) :=
    hcont_ball.mono ball_subset_closedBall
  have heq_on : EqOn u (fun _ => M) (Metric.ball q r) :=
    Measure.eqOn_open_of_ae_eq hae_eq isOpen_ball hcont_u_ball continuousOn_const

  intro y hy
  exact heq_on hy

/-- Strong maximum principle: if $u$ has the volume mean-value property on a connected open set
$\Omega$ and attains its supremum over $\Omega$ at an interior point $p$, then $u$ is constant on
$\Omega$. -/
theorem strong_max_principle {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : HasVolumeMVP u Ω)
    {p : Fin n → ℝ} (hp : p ∈ Ω) (hmax : ∀ x ∈ Ω, u x ≤ u p) :
    ∀ x ∈ Ω, u x = u p := by
  set M := u p with hM_def
  set A := Ω ∩ u ⁻¹' {M}
  set B := Ω ∩ (u ⁻¹' {M})ᶜ
  suffices h : Ω ⊆ A by
    intro x hx; exact (h hx).2

  have hB_open : IsOpen B := by


    show IsOpen (Ω ∩ (u ⁻¹' {M})ᶜ)
    rw [show (u ⁻¹' {M})ᶜ = u ⁻¹' {M}ᶜ from rfl]
    exact hmvp.1.isOpen_inter_preimage hΩo isOpen_compl_singleton

  have hA_open : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro q ⟨hqΩ, hqM⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩo q hqΩ
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro y hy
    have hcball : Metric.closedBall q (r / 2) ⊆ Ω := by
      intro z hz
      exact hball (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hr))
    constructor
    · exact hcball (Metric.ball_subset_closedBall hy)
    · have hmvp_q : u q = ⨍ z in Metric.ball q (r / 2), u z :=
        hmvp.2 q (r / 2) hqΩ (half_pos hr) hcball
      have hle : ∀ z ∈ Metric.ball q (r / 2), u z ≤ M := by
        intro z hz
        exact hmax z (hcball (Metric.ball_subset_closedBall hz))
      exact mvp_max_const_on_ball (half_pos hr) Ω hcball hmvp.1 hmvp_q hle hqM y hy

  by_contra h_not_sub
  obtain ⟨x, hx, hxnA⟩ := not_subset.mp h_not_sub
  have hxB : x ∈ B := ⟨hx, fun hxM => hxnA ⟨hx, hxM⟩⟩
  have hΩA : (Ω ∩ A).Nonempty := ⟨p, hp, hp, rfl⟩
  have hΩB : (Ω ∩ B).Nonempty := ⟨x, hx, hxB⟩
  have hcover : Ω ⊆ A ∪ B := by
    intro z hz
    by_cases h : u z = M
    · left; exact ⟨hz, h⟩
    · right; exact ⟨hz, h⟩
  have hpc : IsPreconnected Ω := hΩc.isPreconnected
  have hΩAB := hpc A B hA_open hB_open hcover hΩA hΩB
  obtain ⟨z, _, hzA, hzB⟩ := hΩAB
  exact hzB.2 hzA.2

/-- Strong minimum principle: if $u$ has the volume mean-value property on a connected open set
$\Omega$ and attains its infimum over $\Omega$ at an interior point $p$, then $u$ is constant on
$\Omega$. -/
theorem strong_min_principle {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : HasVolumeMVP u Ω)
    {p : Fin n → ℝ} (hp : p ∈ Ω) (hmin : ∀ x ∈ Ω, u p ≤ u x) :
    ∀ x ∈ Ω, u x = u p := by
  set v := fun x => -u x
  have hmvp_neg : HasVolumeMVP v Ω := by
    constructor
    · exact hmvp.1.neg
    · intro x R hx hR hball
      have huv := hmvp.2 x R hx hR hball
      show v x = ⨍ y in Metric.ball x R, v y
      simp only [v]
      rw [show (⨍ y in Metric.ball x R, -u y) = -(⨍ y in Metric.ball x R, u y) from by
        simp [MeasureTheory.average, integral_neg]]
      linarith
  have hmax_neg : ∀ x ∈ Ω, v x ≤ v p := fun x hx => by
    simp only [v]; linarith [hmin x hx]
  have h := strong_max_principle hΩo hΩc hmvp_neg hp hmax_neg
  intro x hx
  have := h x hx
  simp only [v] at this
  linarith

set_option maxHeartbeats 800000 in
/-- Weak maximum principle for harmonic functions: if $u$ is harmonic on a bounded connected open
set $\Omega$ and continuous on $\overline{\Omega}$, then for every $x \in \overline{\Omega}$ there
is a point $q \in \partial \Omega$ with $u(x) \leq u(q)$. -/
theorem weak_max_principle {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty)
    {u : (Fin n → ℝ) → ℝ} (hu : IsHarmonic u Ω)
    (hcont : ContinuousOn u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ closure Ω) :
    ∃ q ∈ frontier Ω, u x ≤ u q := by

  have hcompact : IsCompact (closure Ω) := hΩb.isCompact_closure

  have hne_closure : (closure Ω).Nonempty := hΩne.mono subset_closure

  obtain ⟨p, hp_mem, hp_max⟩ := hcompact.exists_isMaxOn hne_closure hcont

  have hp_cases : p ∈ Ω ∨ p ∈ frontier Ω := by
    have h := hp_mem
    rw [closure_eq_interior_union_frontier] at h
    rwa [hΩo.interior_eq] at h
  rcases hp_cases with hp_int | hp_bdy
  ·
    have hmvp : HasVolumeMVP u Ω :=
      ⟨hcont.mono subset_closure, fun y R _ hR hball =>
        CM7.harmonic_volume_mean_value hn hu hR hball⟩
    have hmax_Ω : ∀ y ∈ Ω, u y ≤ u p := fun y hy => hp_max (subset_closure hy)
    have hconst_Ω : ∀ y ∈ Ω, u y = u p :=
      strong_max_principle hΩo hΩc hmvp hp_int hmax_Ω

    have hconst_closure : ∀ y ∈ closure Ω, u y = u p := by
      have h_sub : Ω ⊆ u ⁻¹' {u p} := fun y hy => by simp [hconst_Ω y hy]
      have h_rel_closed : IsClosed (closure Ω ∩ u ⁻¹' {u p}) :=
        hcont.preimage_isClosed_of_isClosed isClosed_closure (isClosed_singleton (x := u p))
      have h_Ω_sub : Ω ⊆ closure Ω ∩ u ⁻¹' {u p} :=
        fun y hy => ⟨subset_closure hy, h_sub hy⟩
      exact fun y hy => (closure_minimal h_Ω_sub h_rel_closed hy).2

    obtain ⟨q, hq⟩ := frontier_nonempty_of_bounded_open_connected hn hΩo hΩc hΩb hΩne
    exact ⟨q, hq, by rw [hconst_closure x hx, hconst_closure q (frontier_subset_closure hq)]⟩
  ·
    exact ⟨p, hp_bdy, hp_max hx⟩

/-- Uniqueness for the Dirichlet problem for Laplace's equation: two harmonic functions on a
bounded connected open set $\Omega$ that agree on the boundary $\partial \Omega$ and are continuous
on $\overline{\Omega}$ agree throughout $\Omega$. -/
theorem dirichlet_uniqueness {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {u₁ u₂ : (Fin n → ℝ) → ℝ}
    (h1 : IsHarmonic u₁ Ω) (h2 : IsHarmonic u₂ Ω)
    (hbdy : ∀ x ∈ frontier Ω, u₁ x = u₂ x)
    (hcont1 : ContinuousOn u₁ (closure Ω))
    (hcont2 : ContinuousOn u₂ (closure Ω)) :
    ∀ x ∈ Ω, u₁ x = u₂ x := by

  set w := fun y => u₁ y - u₂ y
  have hw : IsHarmonic w Ω := h1.sub hΩo h2
  have hw_cont : ContinuousOn w (closure Ω) := hcont1.sub hcont2

  have hw_bdy : ∀ y ∈ frontier Ω, w y = 0 := by
    intro y hy; simp [w, hbdy y hy]
  intro x hx
  have hΩne : Ω.Nonempty := ⟨x, hx⟩

  have hw_le : w x ≤ 0 := by
    obtain ⟨q, hq, hle⟩ := weak_max_principle hn hΩo hΩc hΩb hΩne hw hw_cont x
      (subset_closure hx)
    linarith [hw_bdy q hq]

  have hw_ge : 0 ≤ w x := by
    have hnw : IsHarmonic (fun y => -w y) Ω := hw.neg
    have hnw_cont : ContinuousOn (fun y => -w y) (closure Ω) := hw_cont.neg
    obtain ⟨q, hq, hle⟩ := weak_max_principle hn hΩo hΩc hΩb hΩne hnw hnw_cont x
      (subset_closure hx)
    have : -w q = 0 := by simp [hw_bdy q hq]
    linarith

  have hw_zero : w x = 0 := le_antisymm hw_le hw_ge
  linarith [hw_zero]

/-- Uniqueness for Poisson's equation with Dirichlet boundary data: if $u, v$ both solve
$\Delta u = f$ on a bounded connected open set $\Omega$, are continuous on $\overline{\Omega}$,
and agree on $\partial \Omega$, then $u = v$ on $\overline{\Omega}$. -/
theorem poisson_uniqueness_dirichlet {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {f : (Fin n → ℝ) → ℝ} {u v : (Fin n → ℝ) → ℝ}
    (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
    (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
    (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
    (hbc : ∀ x ∈ frontier Ω, u x = v x) :
    ∀ x ∈ closure Ω, u x = v x := by

  set w := fun x => u x - v x

  have hw : IsHarmonic w Ω :=
    ⟨_hu_reg.sub _hv_reg, fun x hx => by
      rw [laplacian_sub hΩo _hu_reg _hv_reg hx, hu x hx, hv x hx, sub_self]⟩

  have hw_cont : ContinuousOn w (closure Ω) := _hu_cont.sub _hv_cont

  have hw_bdy : ∀ x ∈ frontier Ω, w x = 0 := by
    intro x hx; simp [w, hbc x hx]

  intro x hx
  have hx_cases : x ∈ Ω ∨ x ∈ frontier Ω := by
    rw [closure_eq_interior_union_frontier] at hx
    rwa [hΩo.interior_eq] at hx
  rcases hx_cases with hx_int | hx_bdy
  ·
    have hΩne : Ω.Nonempty := ⟨x, hx_int⟩

    have hw_le : w x ≤ 0 := by
      obtain ⟨q, hq, hle⟩ := weak_max_principle hn hΩo hΩc hΩb hΩne hw hw_cont x
        (subset_closure hx_int)
      linarith [hw_bdy q hq]

    have hw_ge : 0 ≤ w x := by
      have hnw : IsHarmonic (fun y => -w y) Ω := hw.neg
      have hnw_cont : ContinuousOn (fun y => -w y) (closure Ω) := hw_cont.neg
      obtain ⟨q, hq, hle⟩ := weak_max_principle hn hΩo hΩc hΩb hΩne hnw hnw_cont x
        (subset_closure hx_int)
      have : -w q = 0 := by simp [hw_bdy q hq]
      linarith

    have hw_zero : w x = 0 := le_antisymm hw_le hw_ge
    simp [w] at hw_zero ⊢; linarith
  ·
    have := hbc x hx_bdy
    simp at this ⊢; linarith

/-- Comparison principle (strict version): if $u_f, u_g$ are harmonic on a bounded connected open
$\Omega$, continuous on $\overline{\Omega}$, with $u_f \geq u_g$ on $\partial \Omega$ and strict
inequality $u_f > u_g$ at some boundary point, then $u_f > u_g$ throughout $\Omega$. -/
theorem comparison_principle {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {u_f u_g : (Fin n → ℝ) → ℝ}
    (hf : IsHarmonic u_f Ω) (hg : IsHarmonic u_g Ω)
    (hcont_f : ContinuousOn u_f (closure Ω))
    (hcont_g : ContinuousOn u_g (closure Ω))
    (hbdy_ge : ∀ x ∈ frontier Ω, u_f x ≥ u_g x)
    (hbdy_ne : ∃ y ∈ frontier Ω, u_f y > u_g y)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u_f x > u_g x := by

  set w := fun y => u_f y - u_g y
  have hw : IsHarmonic w Ω := hf.sub hΩo hg
  have hw_cont : ContinuousOn w (closure Ω) := hcont_f.sub hcont_g
  have hΩne : Ω.Nonempty := ⟨x, hx⟩

  have hw_bdy_nonneg : ∀ y ∈ frontier Ω, 0 ≤ w y := by
    intro y hy; simp only [w]; linarith [hbdy_ge y hy]

  obtain ⟨y₀, hy₀, hy₀_pos⟩ := hbdy_ne
  have hw_y₀_pos : w y₀ > 0 := by simp only [w]; linarith


  have hw_nonneg : ∀ z ∈ Ω, 0 ≤ w z := by
    intro z hz
    have hnw : IsHarmonic (fun y => -w y) Ω := hw.neg
    have hnw_cont : ContinuousOn (fun y => -w y) (closure Ω) := hw_cont.neg
    obtain ⟨q, hq, hle⟩ := weak_max_principle hn hΩo hΩc hΩb hΩne hnw hnw_cont z
      (subset_closure hz)

    have : -w q ≤ 0 := by linarith [hw_bdy_nonneg q hq]
    linarith


  by_contra h_not_pos
  push Not at h_not_pos

  have hw_x_le : w x ≤ 0 := by simp only [w]; linarith
  have hw_x_zero : w x = 0 := le_antisymm hw_x_le (hw_nonneg x hx)

  have hmin : ∀ z ∈ Ω, w x ≤ w z := by
    intro z hz; rw [hw_x_zero]; exact hw_nonneg z hz

  have hmvp : HasVolumeMVP w Ω :=
    ⟨hw_cont.mono subset_closure, fun y R _ hR hball =>
      CM7.harmonic_volume_mean_value hn hw hR hball⟩

  have hconst : ∀ z ∈ Ω, w z = w x := strong_min_principle hΩo hΩc hmvp hx hmin

  have hconst_zero : ∀ z ∈ Ω, w z = 0 := by
    intro z hz; rw [hconst z hz, hw_x_zero]

  have hconst_closure : ∀ z ∈ closure Ω, w z = 0 := by
    have h_sub : Ω ⊆ w ⁻¹' {0} := fun z hz => by simp [hconst_zero z hz]
    have h_rel_closed : IsClosed (closure Ω ∩ w ⁻¹' {0}) :=
      hw_cont.preimage_isClosed_of_isClosed isClosed_closure (isClosed_singleton (x := (0:ℝ)))
    have h_Ω_sub : Ω ⊆ closure Ω ∩ w ⁻¹' {0} :=
      fun z hz => ⟨subset_closure hz, h_sub hz⟩
    exact fun z hz => (closure_minimal h_Ω_sub h_rel_closed hz).2

  have hw_y₀_zero : w y₀ = 0 := hconst_closure y₀ (frontier_subset_closure hy₀)

  linarith

/-- Stability estimate for Laplace's equation: if $u_f, u_g$ are harmonic on $\Omega$ with boundary
values $f, g$ respectively, and $|f - g| \leq M$ on $\partial \Omega$, then $|u_f - u_g| \leq M$
throughout $\Omega$. -/
theorem laplace_stability_estimate {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {u_f u_g : (Fin n → ℝ) → ℝ}
    (huf : IsHarmonic u_f Ω) (hug : IsHarmonic u_g Ω)
    (huf_cont : ContinuousOn u_f (closure Ω))
    (hug_cont : ContinuousOn u_g (closure Ω))
    {f g : (Fin n → ℝ) → ℝ}
    (huf_bd : ∀ x ∈ frontier Ω, u_f x = f x)
    (hug_bd : ∀ x ∈ frontier Ω, u_g x = g x)
    {M : ℝ} (hM : ∀ y ∈ frontier Ω, |f y - g y| ≤ M)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    |u_f x - u_g x| ≤ M := by

  set w := fun y => u_f y - u_g y
  have hw : IsHarmonic w Ω := huf.sub hΩo hug
  have hw_cont : ContinuousOn w (closure Ω) := huf_cont.sub hug_cont
  have hΩne : Ω.Nonempty := ⟨x, hx⟩

  have hw_bd : ∀ y ∈ frontier Ω, w y = f y - g y := by
    intro y hy; simp [w, huf_bd y hy, hug_bd y hy]
  rw [abs_le]
  constructor
  ·

    have hnw : IsHarmonic (fun y => -w y) Ω := hw.neg
    have hnw_cont : ContinuousOn (fun y => -w y) (closure Ω) := hw_cont.neg
    obtain ⟨q, hq, hle⟩ := weak_max_principle hn hΩo hΩc hΩb hΩne hnw hnw_cont x
      (subset_closure hx)

    have hq_val : -w q = -(f q - g q) := by simp [hw_bd q hq]
    linarith [hM q hq, neg_abs_le (f q - g q)]
  ·

    obtain ⟨q, hq, hle⟩ := weak_max_principle hn hΩo hΩc hΩb hΩne hw hw_cont x
      (subset_closure hx)

    have hq_val : w q = f q - g q := hw_bd q hq
    linarith [hM q hq, le_abs_self (f q - g q)]

/-- Master uniqueness result for Poisson's equation, packaging the four boundary-condition
variants: Dirichlet (unique on $\overline{\Omega}$), Robin with $\alpha > 0$ (unique), Neumann
(unique up to an additive constant), and mixed Dirichlet/Neumann (unique). -/
theorem poisson_uniqueness :

    (∀ {n : ℕ} (hn : 0 < n)
      {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
      (hΩb : Bornology.IsBounded Ω)
      {f : (Fin n → ℝ) → ℝ} {u v : (Fin n → ℝ) → ℝ}
      (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
      (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
      (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
      (hbc : ∀ x ∈ frontier Ω, u x = v x),
      ∀ x ∈ closure Ω, u x = v x) ∧

    (∀ {n : ℕ} (hn : 0 < n)
      {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
      (hΩb : Bornology.IsBounded Ω)
      {f : (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ}
      {α : ℝ} (hα : 0 < α)
      {u v : (Fin n → ℝ) → ℝ}
      (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
      (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
      (_hu_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
      (_hv_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ v x)
      (_hu_fderiv_cont : ContinuousOn (fun x => fderiv ℝ u x) (closure Ω))
      (_hv_fderiv_cont : ContinuousOn (fun x => fderiv ℝ v x) (closure Ω))
      (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
      (hbc_u : ∀ x ∈ frontier Ω, NormalDerivative n u x + α * u x = g x)
      (hbc_v : ∀ x ∈ frontier Ω, NormalDerivative n v x + α * v x = g x),
      ∀ x ∈ closure Ω, u x = v x) ∧

    (∀ {n : ℕ}
      {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
      (hΩb : Bornology.IsBounded Ω)
      {f : (Fin n → ℝ) → ℝ} {h : (Fin n → ℝ) → ℝ}
      {u v : (Fin n → ℝ) → ℝ}
      (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
      (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
      (_hu_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
      (_hv_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ v x)
      (_hu_fderiv_cont : ContinuousOn (fun x => fderiv ℝ u x) (closure Ω))
      (_hv_fderiv_cont : ContinuousOn (fun x => fderiv ℝ v x) (closure Ω))
      (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
      (hbc_u : ∀ x ∈ frontier Ω, NormalDerivative n u x = h x)
      (hbc_v : ∀ x ∈ frontier Ω, NormalDerivative n v x = h x),
      ∃ c : ℝ, ∀ x ∈ closure Ω, u x = v x + c) ∧

    (∀ {n : ℕ}
      {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
      (hΩb : Bornology.IsBounded Ω)
      {f : (Fin n → ℝ) → ℝ}
      {S_D S_N : Set (Fin n → ℝ)}
      (hcover : frontier Ω = S_D ∪ S_N)
      (hdisjoint : Disjoint S_D S_N)
      (hSD_nonempty : S_D.Nonempty)
      {g_D : (Fin n → ℝ) → ℝ} {g_N : (Fin n → ℝ) → ℝ}
      {u v : (Fin n → ℝ) → ℝ}
      (_hu_reg : ContDiffOn ℝ 2 u Ω) (_hv_reg : ContDiffOn ℝ 2 v Ω)
      (_hu_cont : ContinuousOn u (closure Ω)) (_hv_cont : ContinuousOn v (closure Ω))
      (_hu_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
      (_hv_diff_cl : ∀ x ∈ closure Ω, DifferentiableAt ℝ v x)
      (_hu_fderiv_cont : ContinuousOn (fun x => fderiv ℝ u x) (closure Ω))
      (_hv_fderiv_cont : ContinuousOn (fun x => fderiv ℝ v x) (closure Ω))
      (hu : IsPoisson u f Ω) (hv : IsPoisson v f Ω)
      (hbc_u_D : ∀ x ∈ S_D, u x = g_D x) (hbc_v_D : ∀ x ∈ S_D, v x = g_D x)
      (hbc_u_N : ∀ x ∈ S_N, NormalDerivative n u x = g_N x)
      (hbc_v_N : ∀ x ∈ S_N, NormalDerivative n v x = g_N x),
      ∀ x ∈ closure Ω, u x = v x) :=
  ⟨fun {_} hn {_} hΩo hΩc hΩb => poisson_uniqueness_dirichlet hn hΩo hΩc hΩb,
   fun {_} hn {_} hΩo hΩc hΩb => poisson_uniqueness_robin hn hΩo hΩc hΩb,
   fun {_} {_} hΩo hΩc hΩb => poisson_uniqueness_neumann hΩo hΩc hΩb,
   fun {_} {_} hΩo hΩc hΩb => poisson_uniqueness_mixed hΩo hΩc hΩb⟩

end CM7
