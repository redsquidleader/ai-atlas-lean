/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties
import Mathlib.MeasureTheory.Measure.Hausdorff

open Set Metric MeasureTheory

noncomputable section

namespace CM6

/-- Volume mean value property (Theorem 4.1, first formula): if $u$ is harmonic on $\Omega$
and $\overline{B_R(x)} \subset \Omega$, then $u(x)$ equals the average of $u$ over the
ball $B_R(x)$:
$u(x) = \frac{n}{\omega_n R^n} \int_{B_R(x)} u(y) \, d^n y$. -/
theorem harmonic_volume_mean_value {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : CM7.IsHarmonic u Ω)
    {x : Fin n → ℝ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x R ⊆ Ω) :
    u x = ⨍ y in Metric.ball x R, u y :=
  CM7.harmonic_volume_mean_value hn hu hR hball

/-- Spherical mean value property (Theorem 4.1, second formula): if $u$ is harmonic on
$\Omega$ and $\overline{B_R(x)} \subset \Omega$, then $u(x)$ equals the average of $u$
over the sphere $\partial B_R(x)$:
$u(x) = \frac{1}{\omega_n R^{n-1}} \int_{\partial B_R(x)} u(\sigma) \, d\sigma$. -/
theorem harmonic_sphere_mean_value {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : CM7.IsHarmonic u Ω)
    {x : Fin n → ℝ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x R ⊆ Ω) :
    u x = ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + R • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ) := by
  have hu_ball : CM7.IsHarmonic u (Metric.ball x R) :=
    ⟨hu.contDiffOn.mono (Metric.ball_subset_closedBall.trans hball),
     fun y hy => hu.laplacian_eq_zero y (hball (Metric.ball_subset_closedBall hy))⟩

  have key := CM7.harmonic_sphere_mean_value hn u x R hR hu_ball R hR le_rfl

  rw [CM7.sphericalMean, if_neg (ne_of_gt hR)] at key
  exact key.symm

/-- Mean value properties (Theorem 4.1, combined): a harmonic function $u$ on $\Omega$
satisfies both the volume and the spherical mean value formulas on every ball
$\overline{B_R(x)} \subset \Omega$. -/
theorem mean_value_property {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : CM7.IsHarmonic u Ω)
    {x : Fin n → ℝ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall x R ⊆ Ω) :
    (u x = ⨍ y in Metric.ball x R, u y) ∧
    (u x = ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
      u (x + R • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)) :=
  ⟨harmonic_volume_mean_value hn hu hR hball,
   harmonic_sphere_mean_value hn hu hR hball⟩

/-- Strong Maximum Principle (Theorem 5.1, max version): if $u \in C(\Omega)$ verifies the
volume mean value property and attains its maximum at an interior point $p \in \Omega$ of a
connected open set $\Omega$, then $u$ is constant on $\Omega$. -/
theorem strong_maximum_principle {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : CM7.HasVolumeMVP u Ω)
    {p : Fin n → ℝ} (hp : p ∈ Ω) (hmax : ∀ x ∈ Ω, u x ≤ u p) :
    ∀ x ∈ Ω, u x = u p :=
  CM7.strong_max_principle hΩo hΩc hmvp hp hmax

/-- Strong Minimum Principle (Theorem 5.1, min version): if $u \in C(\Omega)$ verifies the
volume mean value property and attains its minimum at an interior point $p \in \Omega$ of
a connected open set $\Omega$, then $u$ is constant on $\Omega$. -/
theorem strong_minimum_principle {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : CM7.HasVolumeMVP u Ω)
    {p : Fin n → ℝ} (hp : p ∈ Ω) (hmin : ∀ x ∈ Ω, u p ≤ u x) :
    ∀ x ∈ Ω, u x = u p :=
  CM7.strong_min_principle hΩo hΩc hmvp hp hmin

/-- Strong Maximum Principle (Theorem 5.1): if $u$ attains either its maximum or its
minimum on $\Omega$ at an interior point, then $u$ is constant on $\Omega$. -/
theorem strong_max_principle_combined {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : CM7.HasVolumeMVP u Ω)
    {p : Fin n → ℝ} (hp : p ∈ Ω)
    (hextreme : (∀ x ∈ Ω, u x ≤ u p) ∨ (∀ x ∈ Ω, u p ≤ u x)) :
    ∀ x ∈ Ω, u x = u p := by
  rcases hextreme with hmax | hmin
  · exact strong_maximum_principle hΩo hΩc hmvp hp hmax
  · exact strong_minimum_principle hΩo hΩc hmvp hp hmin

/-- Strong Maximum Principle on bounded domains (Theorem 5.1 boundary form): if $\Omega$ is
bounded, $u$ verifies the mean value property and is continuous on $\overline{\Omega}$, and
$u$ is non-constant on $\Omega$, then for every $x \in \Omega$ there exist boundary points
$q, q' \in \partial \Omega$ with $u(x) < u(q)$ and $u(q') < u(x)$. -/
theorem strong_max_principle_bounded {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : CM7.HasVolumeMVP u Ω)
    (huc : ContinuousOn u (closure Ω))
    (hnc : ¬ ∀ x ∈ Ω, ∀ y ∈ Ω, u x = u y)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    (∃ q ∈ frontier Ω, u x < u q) ∧ (∃ q ∈ frontier Ω, u q < u x) := by

  have hcompact : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hne_closure : (closure Ω).Nonempty := ⟨x, subset_closure hx⟩

  have hnot_const_at : ¬ ∀ y ∈ Ω, u y = u x := by
    intro hall; exact hnc (fun a ha b hb => by rw [hall a ha, hall b hb])
  constructor
  ·

    obtain ⟨p, hp_mem, hp_max⟩ := hcompact.exists_isMaxOn hne_closure huc


    by_cases hp_in : p ∈ Ω
    ·
      exfalso
      have hmax_Ω : ∀ y ∈ Ω, u y ≤ u p := fun y hy => hp_max (subset_closure hy)
      have := CM7.strong_max_principle hΩo hΩc hmvp hp_in hmax_Ω
      exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)
    ·
      have hp_frontier : p ∈ frontier Ω := by
        rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff]
        exact ⟨hp_mem, by rwa [hΩo.isClosed_compl.closure_eq, Set.mem_compl_iff]⟩
      refine ⟨p, hp_frontier, ?_⟩

      have hle : u x ≤ u p := hp_max (subset_closure hx)
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exfalso
        have hmax_Ω : ∀ y ∈ Ω, u y ≤ u x := fun y hy =>
          heq ▸ hp_max (subset_closure hy)
        have := CM7.strong_max_principle hΩo hΩc hmvp hx hmax_Ω
        exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)
  ·

    obtain ⟨p, hp_mem, hp_min⟩ := hcompact.exists_isMinOn hne_closure huc

    by_cases hp_in : p ∈ Ω
    · exfalso
      have hmin_Ω : ∀ y ∈ Ω, u p ≤ u y := fun y hy => hp_min (subset_closure hy)
      have := CM7.strong_min_principle hΩo hΩc hmvp hp_in hmin_Ω
      exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)
    · have hp_frontier : p ∈ frontier Ω := by
        rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff]
        exact ⟨hp_mem, by rwa [hΩo.isClosed_compl.closure_eq, Set.mem_compl_iff]⟩
      refine ⟨p, hp_frontier, ?_⟩
      have hle : u p ≤ u x := hp_min (subset_closure hx)
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exfalso
        have hmin_Ω : ∀ y ∈ Ω, u x ≤ u y := fun y hy =>
          heq ▸ hp_min (subset_closure hy)
        have := CM7.strong_min_principle hΩo hΩc hmvp hx hmin_Ω
        exact hnot_const_at (fun y hy => (this y hy).trans (this x hx).symm)

/-- Strong Maximum Principle in sup/inf form (Theorem 5.1): for a non-constant $u$ on a
bounded, connected open $\Omega$ with the mean value property and continuous on
$\overline{\Omega}$, every interior $x \in \Omega$ satisfies
$\inf_{\partial \Omega} u < u(x) < \sup_{\partial \Omega} u$. -/
theorem strong_max_principle_boundary_bounds {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : CM7.HasVolumeMVP u Ω)
    (huc : ContinuousOn u (closure Ω))
    (hnc : ¬ ∀ x ∈ Ω, ∀ y ∈ Ω, u x = u y)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    u x < sSup (u '' frontier Ω) ∧ sInf (u '' frontier Ω) < u x := by
  obtain ⟨⟨q₁, hq₁f, hlt₁⟩, ⟨q₂, hq₂f, hlt₂⟩⟩ :=
    strong_max_principle_bounded hΩo hΩc hΩb hmvp huc hnc hx
  have hfr_compact : IsCompact (frontier Ω) :=
    hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfr_img_bdd : BddAbove (u '' frontier Ω) :=
    (hfr_compact.image_of_continuousOn (huc.mono frontier_subset_closure)).isBounded.bddAbove
  have hfr_img_bdd_below : BddBelow (u '' frontier Ω) :=
    (hfr_compact.image_of_continuousOn (huc.mono frontier_subset_closure)).isBounded.bddBelow
  exact ⟨lt_of_lt_of_le hlt₁ (le_csSup hfr_img_bdd ⟨q₁, hq₁f, rfl⟩),
         lt_of_le_of_lt (csInf_le hfr_img_bdd_below ⟨q₂, hq₂f, rfl⟩) hlt₂⟩

/-- Combined statement of the Strong Maximum Principle (Theorem 5.1): interior extrema
force the function to be constant, and for non-constant solutions every interior value is
strictly between the boundary infimum and supremum. -/
theorem strong_maximum_principle_full {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : CM7.HasVolumeMVP u Ω)
    (huc : ContinuousOn u (closure Ω)) :

    (∀ p ∈ Ω, (∀ x ∈ Ω, u x ≤ u p) ∨ (∀ x ∈ Ω, u p ≤ u x) →
      ∀ x ∈ Ω, u x = u p)
    ∧

    (¬(∀ x ∈ Ω, ∀ y ∈ Ω, u x = u y) →
      ∀ x ∈ Ω, u x < sSup (u '' frontier Ω) ∧ sInf (u '' frontier Ω) < u x) :=
  ⟨fun _p hp hextreme => strong_max_principle_combined hΩo hΩc hmvp hp hextreme,
   fun hnc _x hx => strong_max_principle_boundary_bounds hΩo hΩc hΩb hmvp huc hnc hx⟩

/-- Corollary 5.0.1: for the Dirichlet problem $\Delta u = 0$ in $\Omega$, $u = f$ on
$\partial \Omega$ on a bounded, connected open $\Omega \subset \mathbb{R}^n$, the following
hold: (1) uniqueness of harmonic solutions sharing boundary values; (2) a comparison
principle — if the boundary data satisfies $f \geq g$ with strict inequality somewhere,
then $u_f > u_g$ in $\Omega$; (3) a stability estimate $|u_f - u_g| \leq M$ in $\Omega$
whenever $|f - g| \leq M$ on $\partial \Omega$. -/
theorem dirichlet_uniqueness_comparison_stability {n : ℕ} (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω) :

    (∀ u₁ u₂ : (Fin n → ℝ) → ℝ,
      CM7.IsHarmonic u₁ Ω → CM7.IsHarmonic u₂ Ω →
      (∀ x ∈ frontier Ω, u₁ x = u₂ x) →
      ContinuousOn u₁ (closure Ω) → ContinuousOn u₂ (closure Ω) →
      ∀ x ∈ Ω, u₁ x = u₂ x)
    ∧

    (∀ u_f u_g : (Fin n → ℝ) → ℝ,
      CM7.IsHarmonic u_f Ω → CM7.IsHarmonic u_g Ω →
      ContinuousOn u_f (closure Ω) → ContinuousOn u_g (closure Ω) →
      (∀ x ∈ frontier Ω, u_f x ≥ u_g x) →
      (∃ y ∈ frontier Ω, u_f y > u_g y) →
      ∀ x ∈ Ω, u_f x > u_g x)
    ∧

    (∀ u_f u_g : (Fin n → ℝ) → ℝ,
      CM7.IsHarmonic u_f Ω → CM7.IsHarmonic u_g Ω →
      ContinuousOn u_f (closure Ω) → ContinuousOn u_g (closure Ω) →
      ∀ f g : (Fin n → ℝ) → ℝ, ∀ M : ℝ,
      (∀ x ∈ frontier Ω, u_f x = f x) →
      (∀ x ∈ frontier Ω, u_g x = g x) →
      (∀ y ∈ frontier Ω, |f y - g y| ≤ M) →
      ∀ x ∈ Ω, |u_f x - u_g x| ≤ M) :=
  ⟨fun _ _ h1 h2 hbdy hcont1 hcont2 =>
      CM7.dirichlet_uniqueness hn hΩo hΩc hΩb h1 h2 hbdy hcont1 hcont2,
   fun _ _ hf hg hcont_f hcont_g hbdy_ge hbdy_ne x hx =>
      CM7.comparison_principle hn hΩo hΩc hΩb hf hg hcont_f hcont_g hbdy_ge hbdy_ne x hx,
   fun _ _ huf hug huf_cont hug_cont _ _ _ huf_bd hug_bd hM x hx =>
      CM7.laplace_stability_estimate hn hΩo hΩc hΩb huf hug huf_cont hug_cont
        huf_bd hug_bd hM x hx⟩

end CM6
