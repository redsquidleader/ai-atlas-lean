/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas

open Real Set MeasureTheory Classical

noncomputable section

namespace CM8

/-- Theorem 2.1 (basic existence and uniqueness for the Dirichlet problem):
on a bounded Lipschitz domain $\Omega \subset \mathbb{R}^n$ ($n \geq 2$) with
continuous boundary data $g \in C(\partial \Omega)$, the Poisson problem
$\Delta u = f$ in $\Omega$ with $u = g$ on $\partial \Omega$ has a unique solution
$u \in C^2(\Omega) \cap C(\overline{\Omega})$. -/
theorem dirichlet_existence (n : ℕ) [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (hΩ_open : IsOpen Ω) (hΩ_bounded : Bornology.IsBounded Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ) (hg : ContinuousOn g (frontier Ω)) :
    ∃ u : (Fin n → ℝ) → ℝ,
      ContDiffOn ℝ 2 u Ω ∧
      ContinuousOn u (closure Ω) ∧
      (∀ x ∈ Ω, laplacian u x = f x) ∧
      (∀ x ∈ frontier Ω, u x = g x) ∧
      (∀ u' : (Fin n → ℝ) → ℝ,
        ContDiffOn ℝ 2 u' Ω →
        ContinuousOn u' (closure Ω) →
        (∀ x ∈ Ω, laplacian u' x = f x) →
        (∀ x ∈ frontier Ω, u' x = g x) →
        ∀ x ∈ closure Ω, u' x = u x) := by sorry

/-- Proposition 2.0.2 (Green function decomposition): the Green function of $\Omega$
can be written as $G(x, y) = \Phi(x - y) - \varphi(x, y)$, where for each fixed
$x \in \Omega$ the corrector $\varphi(x, \cdot)$ solves the Dirichlet problem
$\Delta_y \varphi(x, y) = 0$ in $\Omega$ with $\varphi(x, \sigma) = \Phi(x - \sigma)$
on $\partial \Omega$. -/
theorem green_function_decomposition (n : ℕ) [hn : Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (hΩ_open : IsOpen Ω) (hΩ_bounded : Bornology.IsBounded Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (hΦ_cont : ∀ x ∈ Ω, ContinuousOn (fun σ => FundSolN (x - σ)) (frontier Ω)) :
    ∃ φ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ,

      (∀ x ∈ Ω, ContDiffOn ℝ 2 (φ x) Ω) ∧

      (∀ x ∈ Ω, ContinuousOn (φ x) (closure Ω)) ∧

      (∀ x ∈ Ω, ∀ y ∈ Ω, laplacian (φ x) y = 0) ∧

      (∀ x ∈ Ω, ∀ σ ∈ frontier Ω, φ x σ = FundSolN (x - σ)) ∧

      (∀ x ∈ Ω, ∀ σ ∈ frontier Ω, FundSolN (x - σ) - φ x σ = 0) := by

  have h_exist : ∀ x ∈ Ω, ∃ u : (Fin n → ℝ) → ℝ,
      ContDiffOn ℝ 2 u Ω ∧
      ContinuousOn u (closure Ω) ∧
      (∀ y ∈ Ω, laplacian u y = (fun _ => (0 : ℝ)) y) ∧
      (∀ σ ∈ frontier Ω, u σ = FundSolN (x - σ)) ∧
      (∀ u' : (Fin n → ℝ) → ℝ,
        ContDiffOn ℝ 2 u' Ω →
        ContinuousOn u' (closure Ω) →
        (∀ y ∈ Ω, laplacian u' y = (fun _ => (0 : ℝ)) y) →
        (∀ σ ∈ frontier Ω, u' σ = FundSolN (x - σ)) →
        ∀ y ∈ closure Ω, u' y = u y) := by
    intro x hx
    exact dirichlet_existence n Ω hΩ_open hΩ_bounded hΩ_lip
      (fun _ => 0) (fun σ => FundSolN (x - σ)) (hΦ_cont x hx)

  choose! u hu using h_exist

  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx; exact (hu x hx).1
  ·
    intro x hx; exact (hu x hx).2.1
  ·
    intro x hx y hy
    have := (hu x hx).2.2.1 y hy
    simpa using this
  ·
    intro x hx σ hσ; exact (hu x hx).2.2.2.1 σ hσ
  ·
    intro x hx σ hσ
    rw [(hu x hx).2.2.2.1 σ hσ]; ring

end CM8
