/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option autoImplicit false

namespace Donaldson

noncomputable section

open Real


/-- Data for a compact Kähler manifold: a metric space $M$, complex dimension $n$, a
non-degenerate antisymmetric 2-form $\omega$, an almost complex structure $J$ with $J^2 = -I$,
the Kähler metric $g(v,w) = \omega(v, J w)$, and an integrality condition on the symplectic
volume (needed for Donaldson's pre-quantization). -/
structure CompactKahlerData where
  M : Type*
  metricInst : MetricSpace M
  compactInst : @CompactSpace M metricInst.toUniformSpace.toTopologicalSpace
  complexDim : ℕ
  dim_pos : 0 < complexDim
  ω : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ) → ℝ
  ω_antisymm : ∀ p v w, ω p v w = -(ω p w v)
  J : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ)
  J_sq_neg : ∀ p v, J p (J p v) = fun i => -(v i)
  g : M → (Fin (2 * complexDim) → ℝ) → (Fin (2 * complexDim) → ℝ) → ℝ
  kahler_compat : ∀ p v w, g p v w = ω p v (J p w)
  symplectic_volume : ℝ
  symplectic_volume_pos : 0 < symplectic_volume
  integrality_condition : ∃ (N : ℕ), 0 < N ∧
    symplectic_volume = (2 * Real.pi) ^ complexDim * ↑N

/-- A family $\{\sigma_{k,p}\}$ of sections indexed by an integer $k$ and a basepoint $p \in M$. -/
structure SectionFamily (X : CompactKahlerData) where
  section_ : ℕ → X.M → X.M → ℂ

/-- Abstraction of the $k$-weighted $C^r$ sup-norm $\sup_x (k^{r/2}|\nabla^r s(x)|)$, with the
basic properties (non-negativity, neg-invariance, and pointwise control for $r=0$). -/
structure WeightedSupNorm (X : CompactKahlerData) where
  eval : ℕ → ℕ → (X.M → ℂ) → ℝ
  nonneg : ∀ k r s, 0 ≤ eval k r s
  neg_le : ∀ k r s, eval k r (fun x => -(s x)) ≤ eval k r s
  pointwise_control : ∀ k s (B : ℝ), 0 ≤ B → (∀ x : X.M, ‖s x‖ ≤ B) → eval k 0 s ≤ B

/-- Abstraction of an $L^2$ norm on sections, with the basic property of non-negativity. -/
structure L2Norm (X : CompactKahlerData) where
  norm : (X.M → ℂ) → ℝ
  nonneg : ∀ s, 0 ≤ norm s

/-- Abstraction of the Dolbeault operator $\bar\partial$ on sections of $L^k$, together with the
pointwise estimate that $|\bar\partial$ applied to the Gaussian peak section$|\leq C/\sqrt k$. -/
structure DelbarOp (X : CompactKahlerData) where
  delbar : (X.M → ℂ) → (X.M → ℂ)
  delbar_gaussian_pointwise_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, ∀ p x : X.M,
      ‖delbar (fun q => (Real.exp (-(↑k : ℝ) *
        (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 / 4) : ℂ)) x‖ ≤
        C / Real.sqrt (↑k)


variable {X : CompactKahlerData}

/-- The family $\{\sigma_{k,p}\}$ is uniformly $C^r$-bounded for every $r$. -/
def IsUniformlyBounded (wdn : WeightedSupNorm X) (fam : SectionFamily X) : Prop :=
  ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
    ∀ k : ℕ, ∀ p : X.M, wdn.eval k r (fam.section_ k p) ≤ C_r

/-- The family is approximately holomorphic: $\|\bar\partial \sigma_{k,p}\|_{C^r} \leq C_r/\sqrt{k}$. -/
def IsApproxHolomorphic (wdn : WeightedSupNorm X) (dol : DelbarOp X)
    (fam : SectionFamily X) : Prop :=
  ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
    ∀ k : ℕ, ∀ p : X.M, wdn.eval k r (dol.delbar (fam.section_ k p)) ≤
      C_r / Real.sqrt (↑k)

/-- The family is uniformly Gaussian-concentrated around $p$:
$|\sigma_{k,p}(x)| \leq C \exp(-\lambda k\, d(p,x)^2)$. -/
def IsUniformlyConcentrated (fam : SectionFamily X) : Prop :=
  ∃ C lam : ℝ, C > 0 ∧ lam > 0 ∧
    ∀ k : ℕ, ∀ p x : X.M, ‖fam.section_ k p x‖ ≤
      C * Real.exp (-lam * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2)

/-- A family is truly holomorphic if $\bar\partial \sigma_{k,p} = 0$ for all $k, p$. -/
def IsHolomorphicFamily (dol : DelbarOp X) (fam : SectionFamily X) : Prop :=
  ∀ k : ℕ, ∀ p : X.M, dol.delbar (fam.section_ k p) = 0

/-- Two families are exponentially close in every $C^r$-norm:
$\|\sigma_{k,p} - \tilde\sigma_{k,p}\|_{C^r} \leq C_r \exp(-\lambda k^{1/3})$. -/
def IsExponentiallyClose (wdn : WeightedSupNorm X)
    (fam fam' : SectionFamily X) : Prop :=
  ∃ lam : ℝ, lam > 0 ∧
    ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
      ∀ k : ℕ, ∀ p : X.M,
        wdn.eval k r (fun x => fam.section_ k p x - fam'.section_ k p x) ≤
          C_r * Real.exp (-lam * (↑k) ^ ((1 : ℝ) / 3))


/-- The Gaussian peak section family $\sigma_{k,p}(q) = e^{-k\, d(p,q)^2/4}$ used as a model
for Donaldson's near-holomorphic peak sections. -/
def gaussianPeakSection (X : CompactKahlerData) : SectionFamily X :=
  { section_ := fun k p q =>
      (Real.exp (-(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 / 4) : ℂ) }


/-- The Gaussian peak section is pointwise bounded by 1 since $e^{-k d^2/4} \leq 1$. -/
theorem gaussian_pointwise_le_one (X : CompactKahlerData) (k : ℕ) (p x : X.M) :
    ‖(gaussianPeakSection X).section_ k p x‖ ≤ 1 := by
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg' k
  nlinarith [sq_nonneg (@Dist.dist X.M X.metricInst.toDist p x)]


/-- The Gaussian peak section is uniformly concentrated with constants $C = 1$, $\lambda = 1/4$. -/
theorem gaussian_peak_concentrated (X : CompactKahlerData) :
    IsUniformlyConcentrated (gaussianPeakSection X) := by
  refine ⟨(1 : ℝ), (1 : ℝ)/4, by norm_num, by norm_num, ?_⟩
  intro k p x
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

  have heq : -(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 / 4 =
      -(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 := by ring
  linarith [exp_pos (-(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2),
            show exp (-(↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2 / 4) =
                 exp (-(1/4 : ℝ) * ↑k * (@Dist.dist X.M X.metricInst.toDist p x) ^ 2) from
              congrArg exp heq]


/-- Lower bound on the Gaussian peak section within a $1/\sqrt{k}$-ball:
$|\sigma_{k,p}(q)| \geq e^{-1/4}$ when $d(p,q) \leq 1/\sqrt{k}$. -/
theorem gaussian_peak_lower_bound (X : CompactKahlerData) :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, 1 < k → ∀ p q : X.M,
      @Dist.dist X.M X.metricInst.toDist p q ≤ 1 / Real.sqrt (↑k) →
      c ≤ ‖(gaussianPeakSection X).section_ k p q‖ := by
  refine ⟨Real.exp (-(1:ℝ)/4), exp_pos _, ?_⟩
  intro k hk p q hdist
  simp only [gaussianPeakSection]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr

  have hk' : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hk)
  have hdist_nn : (0 : ℝ) ≤ @Dist.dist X.M X.metricInst.toDist p q :=
    @dist_nonneg X.M X.metricInst.toPseudoMetricSpace p q

  have hd_sq : (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ 1 / ↑k := by
    have h2 : (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ (1 / Real.sqrt ↑k) ^ 2 :=
      sq_le_sq' (by linarith) hdist
    calc _ ≤ (1 / Real.sqrt ↑k) ^ 2 := h2
      _ = 1 / (Real.sqrt ↑k) ^ 2 := by ring
      _ = 1 / ↑k := by rw [sq_sqrt (le_of_lt hk')]

  have hkd : (↑k : ℝ) * (@Dist.dist X.M X.metricInst.toDist p q) ^ 2 ≤ 1 :=
    calc (↑k : ℝ) * _ ≤ ↑k * (1 / ↑k) := mul_le_mul_of_nonneg_left hd_sq (le_of_lt hk')
      _ = 1 := by field_simp

  nlinarith


/-- Higher derivatives of the Gaussian peak section are uniformly bounded in the weighted norm. -/
theorem gaussian_peak_higher_derivatives_bounded (X : CompactKahlerData)
    (wdn : WeightedSupNorm X) :
    ∀ r : ℕ, 0 < r → ∃ C_r : ℝ, C_r > 0 ∧
      ∀ k : ℕ, ∀ p : X.M, wdn.eval k r ((gaussianPeakSection X).section_ k p) ≤ C_r := by sorry

/-- Higher derivatives of $\bar\partial$ applied to the Gaussian peak section decay like
$1/\sqrt{k}$ in the weighted norm. -/
theorem delbar_gaussian_higher_derivatives_bounded (X : CompactKahlerData)
    (wdn : WeightedSupNorm X) (dol : DelbarOp X) :
    ∀ r : ℕ, 0 < r → ∃ C_r : ℝ, C_r > 0 ∧
      ∀ k : ℕ, ∀ p : X.M,
        wdn.eval k r (dol.delbar ((gaussianPeakSection X).section_ k p)) ≤
          C_r / Real.sqrt (↑k) := by sorry


/-- The Gaussian peak section family is uniformly $C^r$-bounded for all $r$. -/
theorem gaussian_peak_bounded (X : CompactKahlerData) (wdn : WeightedSupNorm X) :
    IsUniformlyBounded wdn (gaussianPeakSection X) := by
  intro r
  by_cases hr : r = 0
  ·
    subst hr
    refine ⟨1, by norm_num, ?_⟩
    intro k p
    exact wdn.pointwise_control k _ 1 (by norm_num) (gaussian_pointwise_le_one X k p)
  ·
    exact gaussian_peak_higher_derivatives_bounded X wdn r (Nat.pos_of_ne_zero hr)


/-- The Gaussian peak section family is approximately holomorphic: $\bar\partial$ decays as $1/\sqrt k$. -/
theorem gaussian_peak_approx_holo (X : CompactKahlerData)
    (wdn : WeightedSupNorm X) (dol : DelbarOp X) :
    IsApproxHolomorphic wdn dol (gaussianPeakSection X) := by
  intro r
  by_cases hr : r = 0
  ·
    subst hr
    obtain ⟨C, hC, hbound⟩ := dol.delbar_gaussian_pointwise_bound
    refine ⟨C, hC, ?_⟩
    intro k p
    have hnn : (0 : ℝ) ≤ C / Real.sqrt (↑k) :=
      div_nonneg (le_of_lt hC) (Real.sqrt_nonneg _)
    exact le_trans (wdn.pointwise_control k _ _ hnn (hbound k p)) (le_refl _)
  ·
    exact delbar_gaussian_higher_derivatives_bounded X wdn dol r (Nat.pos_of_ne_zero hr)


/-- Construction of peak sections (Step 1 of Donaldson's proof): there exists a family of
sections that is uniformly bounded, approximately holomorphic, uniformly concentrated, and
bounded below on $1/\sqrt{k}$-balls. -/
theorem peak_section_construction (X : CompactKahlerData)
    (wdn : WeightedSupNorm X) (dol : DelbarOp X) :
    ∃ (fam : SectionFamily X) (k₀ : ℕ),
      1 ≤ k₀ ∧
      IsUniformlyBounded wdn fam ∧
      IsApproxHolomorphic wdn dol fam ∧
      IsUniformlyConcentrated fam ∧
      (∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k₀ < k → ∀ p q : X.M,
        @Dist.dist X.M X.metricInst.toDist p q ≤ 1 / Real.sqrt (↑k) →
        c ≤ ‖fam.section_ k p q‖) := by

  refine ⟨gaussianPeakSection X, 2, by omega, ?_, ?_, ?_, ?_⟩

  · exact gaussian_peak_bounded X wdn

  · exact gaussian_peak_approx_holo X wdn dol

  · exact gaussian_peak_concentrated X

  · obtain ⟨c, hc, hlower⟩ := gaussian_peak_lower_bound X
    exact ⟨c, hc, fun k hk => hlower k (by omega)⟩


/-- Sub-exponential decay of $\bar\partial$ of a cutoff section in $L^2$:
$\|\bar\partial \sigma_{k,p}\|_{L^2} \leq C_g \exp(-\lambda k^{1/3})$. -/
theorem cutoff_delbar_decay (X : CompactKahlerData)
    (l2 : L2Norm X) (dol : DelbarOp X) (fam : SectionFamily X) :
    ∃ C_g lam : ℝ, C_g > 0 ∧ lam > 0 ∧
      ∀ k : ℕ, ∀ p : X.M,
        l2.norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (↑k) ^ ((1 : ℝ) / 3)) := by sorry

/-- Existence of a Green's operator correction: for each $k$ and each section $s$, there is a
correction whose $L^2$ norm is bounded by $c_G/\sqrt{k}$ times $\|\bar\partial s\|_{L^2}$, and
which makes $s + \mathrm{corr}(s)$ truly holomorphic. -/
theorem green_correction_exists (X : CompactKahlerData)
    (l2 : L2Norm X) (dol : DelbarOp X) :
    ∃ (greenCorr : ℕ → (X.M → ℂ) → (X.M → ℂ)),
      (∀ k : ℕ, k ≠ 0 → ∀ s : X.M → ℂ,
        dol.delbar (fun x => s x + greenCorr k s x) = 0) ∧
      (∀ s : X.M → ℂ,
        dol.delbar (fun x => s x + greenCorr 0 s x) = 0) ∧
      (∃ c_G : ℝ, c_G > 0 ∧ ∀ k : ℕ, k ≠ 0 → ∀ s : X.M → ℂ,
        l2.norm (greenCorr k s) ≤ c_G / Real.sqrt (↑k) * l2.norm (dol.delbar s)) := by sorry

/-- Elliptic Cauchy estimates: the $C^r$-norm of the Green correction is controlled by the
$L^2$-norm of $\bar\partial s$. -/
theorem cauchy_l2_to_cr_estimates (X : CompactKahlerData)
    (wdn : WeightedSupNorm X) (l2 : L2Norm X) (dol : DelbarOp X)
    (greenCorr : ℕ → (X.M → ℂ) → (X.M → ℂ)) :
    ∀ r : ℕ, ∃ C_r : ℝ, C_r > 0 ∧
      ∀ k : ℕ, ∀ s : X.M → ℂ,
        wdn.eval k r (greenCorr k s) ≤ C_r * l2.norm (dol.delbar s) := by sorry


/-- Donaldson's Proposition 1 on approximately holomorphic sections: there exists a peak section
family $\{\sigma_{k,p}\}$ and a truly holomorphic family $\{\tilde\sigma_{k,p}\}$ with
$\sup |\sigma_{k,p} - \tilde\sigma_{k,p}|_{C^r} \leq O(\exp(-\lambda k^{1/3}))$. -/
theorem donaldson_proposition_1_book
    (X : CompactKahlerData)
    (wdn : WeightedSupNorm X)
    (l2 : L2Norm X)
    (dol : DelbarOp X) :
    ∃ (fam : SectionFamily X) (k₀ : ℕ),
      1 ≤ k₀ ∧
      IsUniformlyBounded wdn fam ∧
      IsApproxHolomorphic wdn dol fam ∧
      IsUniformlyConcentrated fam ∧
      (∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k₀ < k → ∀ p q : X.M,
        @Dist.dist X.M X.metricInst.toDist p q ≤ 1 / Real.sqrt (↑k) →
        c ≤ ‖fam.section_ k p q‖) ∧
      (∃ fam' : SectionFamily X,
        IsHolomorphicFamily dol fam' ∧
        IsExponentiallyClose wdn fam fam') := by


  have _hkahler := X.kahler_compat


  have _hintegral := X.integrality_condition

  obtain ⟨fam, k₀, hk₀, hbound, happrox, hconc, hpeak_lower⟩ :=
    peak_section_construction X wdn dol

  obtain ⟨C_g, lam, hCg, hlam, hdelbar⟩ := cutoff_delbar_decay X l2 dol fam

  obtain ⟨greenCorr, hgreen_hol, hgreen_zero, _⟩ := green_correction_exists X l2 dol

  have hcauchy := cauchy_l2_to_cr_estimates X wdn l2 dol greenCorr

  let fam' : SectionFamily X :=
    { section_ := fun k p x => fam.section_ k p x + greenCorr k (fam.section_ k p) x }

  have hhol : IsHolomorphicFamily dol fam' := by
    intro k p
    by_cases hk : k = 0
    · subst hk; exact hgreen_zero (fam.section_ 0 p)
    · exact hgreen_hol k hk (fam.section_ k p)

  have hclose : IsExponentiallyClose wdn fam fam' := by
    refine ⟨lam, hlam, ?_⟩
    intro r
    obtain ⟨C_r, hCr_pos, hCr⟩ := hcauchy r
    refine ⟨C_r * C_g, mul_pos hCr_pos hCg, ?_⟩
    intro k p
    have h_diff : (fun x => fam.section_ k p x - fam'.section_ k p x) =
        (fun x => -(greenCorr k (fam.section_ k p) x)) := by
      ext x; simp only [fam']; ring
    rw [h_diff]
    calc wdn.eval k r (fun x => -(greenCorr k (fam.section_ k p) x))
        ≤ wdn.eval k r (greenCorr k (fam.section_ k p)) :=
          wdn.neg_le k r (greenCorr k (fam.section_ k p))
      _ ≤ C_r * l2.norm (dol.delbar (fam.section_ k p)) :=
          hCr k (fam.section_ k p)
      _ ≤ C_r * (C_g * exp (-lam * ↑k ^ ((1 : ℝ) / 3))) := by
          apply mul_le_mul_of_nonneg_left (hdelbar k p) (le_of_lt hCr_pos)
      _ = C_r * C_g * exp (-lam * ↑k ^ ((1 : ℝ) / 3)) := by ring

  exact ⟨fam, k₀, hk₀, hbound, happrox, hconc, hpeak_lower, fam', hhol, hclose⟩

end

end Donaldson
