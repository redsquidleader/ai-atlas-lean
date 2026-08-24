/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

noncomputable section

open MeasureTheory Metric Set Finset
open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- The perpendicular direction in $\mathbb{R}^2$: rotates a vector $(e_0, e_1)$ to
$(-e_1, e_0)$. -/
def perpDir (e : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
    if i = (0 : Fin 2) then -(EuclideanSpace.equiv (Fin 2) ℝ e 1)
    else EuclideanSpace.equiv (Fin 2) ℝ e 0)

/-- The rectangle in $\mathbb{R}^2$ centered at `center` with major axis along `dir`,
of half-length `halfLength` along `dir` and half-width `halfWidth` along `perpDir dir`. -/
def rectangleSet (center : EuclideanSpace ℝ (Fin 2))
    (dir : EuclideanSpace ℝ (Fin 2)) (halfWidth halfLength : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |⟪x - center, dir⟫_ℝ| ≤ halfLength ∧
       |⟪x - center, perpDir dir⟫_ℝ| ≤ halfWidth}

/-- A $1 \times R$ tube in $\mathbb{R}^2$: a long, thin rectangle with unit direction
vector, length `R ≥ 1`, and width $1$. -/
structure Tube where
  R : ℝ
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1
  hR : 1 ≤ R

/-- Realize a `Tube` as the set $\{x \in \mathbb{R}^2 : |\langle x - c, d\rangle| \leq R/2,
\ |\langle x - c, d^\perp\rangle| \leq 1/2\}$. -/
def Tube.asSet (T : Tube) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleSet T.center T.direction (1/2) (T.R/2)

/-- The two-dimensional Fourier transform $\hat f(\xi) = \int f(x) e^{-2\pi i \langle x,
\xi\rangle}\, dx$ of a real-valued function on $\mathbb{R}^2$, returning a complex value. -/
def fourierTransformR2 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (EuclideanSpace ℝ (Fin 2))) (fun x => (f x : ℂ)) ξ

/-- The set of dyadic scales between $1$ and $R$: $\{2^k : k \in \mathbb{N}, 1 \leq 2^k \leq R\}$. -/
def dyadicScales (R : ℝ) : Set ℝ :=
  {r : ℝ | ∃ k : ℕ, r = 2 ^ k ∧ 1 ≤ r ∧ r ≤ R}

/-- A collection of $1 \times R$ tubes in $\mathbb{R}^2$ together with smooth bump
functions $\psi_i$ adapted to each tube and a (compactly supported) Fourier bound.
This is the data $f = \sum_T \psi_T$ used in the real-version Main Lemma 2R. -/
structure TubeCollection where
  R : ℝ
  hR : 1 ≤ R
  ι : Type
  [hι : Fintype ι]
  tubes : ι → Tube
  tubes_scale : ∀ i, (tubes i).R = R
  ψ : ι → (EuclideanSpace ℝ (Fin 2) → ℝ)
  ψ_smooth : ∀ i, ContDiff ℝ ⊤ (ψ i)
  ψ_integrable : ∀ i, Integrable (ψ i) volume
  fourierSupportBound : ℝ
  ψ_fourier_compact_support : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > fourierSupportBound → fourierTransformR2 (ψ i) ξ = 0

/-- The index type of a `TubeCollection` is a `Fintype`. -/
instance (S : TubeCollection) : Fintype S.ι := S.hι

/-- The aggregated tube sum $f(x) = \sum_i \psi_i(x)$. -/
def TubeCollection.tubeSum (S : TubeCollection) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i : S.ι, S.ψ i x

/-- The number of tubes in `S` contained in the $r \times R$ rectangle with center `c`
and direction `d`. -/
def TubeCollection.countContained (S : TubeCollection) (r : ℝ)
    (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (Finset.univ.filter fun j =>
    (S.tubes j).asSet ⊆ rectangleSet c d r S.R).card

/-- The multiplicity at scale $r$: the maximum, over all $r \times R$ rectangles, of the
number of tubes of `S` contained in that rectangle. -/
def TubeCollection.multiplicity (S : TubeCollection) (r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)),
    n = S.countContained r c d}

/-- A frequency decomposition $f = \sum_{r} f_r$ of the tube sum into pieces with
Fourier support in $\{|\xi| \leq 1/r\}$, satisfying a near-orthogonality $L^2$ bound. -/
structure FrequencyDecomposition (S : TubeCollection) where
  f_r : ℝ → (EuclideanSpace ℝ (Fin 2) → ℝ)
  scales : Finset ℝ
  scales_range : ∀ r ∈ scales, r ∈ dyadicScales S.R
  sum_eq : ∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x
  fourier_support : ∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0
  near_orthogonality : ∃ (C_orth : ℝ), 0 < C_orth ∧
    ∑ r ∈ scales, ∫ x, (f_r r x) ^ 2 ≤ C_orth * ∫ x, (S.tubeSum x) ^ 2

/-- **Plancherel** for the 2D Fourier transform of a real-valued function:
$\int |f(x)|^2\, dx = \int |\hat f(\xi)|^2\, d\xi$. -/
theorem plancherel_fourierTransformR2
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ∫ x, (f x) ^ 2 = ∫ ξ, ‖fourierTransformR2 f ξ‖ ^ 2 := by sorry

/-- Bilinear Plancherel/Parseval identity: $\int f(x) g(x)\, dx = \mathrm{Re}\,\int
\hat f(\xi) \overline{\hat g(\xi)}\, d\xi$. -/
theorem plancherel_bilinear_fourierTransformR2
    (f g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    (∫ x, f x * g x : ℝ) =
      ∫ ξ, (fourierTransformR2 f ξ * starRingEnd ℂ (fourierTransformR2 g ξ)).re := by sorry

/-- **Pointwise bounded overlap on the Fourier side.** For a decomposition
$f = \sum_r f_r$ with $\hat{f_r}$ supported in $\{|\xi| \leq 1/r\}$, there is a constant
$C$ such that the dyadic Fourier supports overlap with bounded multiplicity:
$\sum_r |\hat{f_r}(\xi)|^2 \leq C |\hat f(\xi)|^2$ for every $\xi$. -/
theorem bounded_overlap_fourier_pointwise
    (f_r : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (scales : Finset ℝ)
    (h_sum : ∀ x, f x = ∑ r ∈ scales, f_r r x)
    (h_support : ∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0) :
    ∃ (C : ℝ), 0 < C ∧
      (∀ r ∈ scales, Integrable (fun ξ => ‖fourierTransformR2 (f_r r) ξ‖ ^ 2) volume) ∧
      (Integrable (fun ξ => ‖fourierTransformR2 f ξ‖ ^ 2) volume) ∧
      (∀ ξ : EuclideanSpace ℝ (Fin 2),
        ∑ r ∈ scales, ‖fourierTransformR2 (f_r r) ξ‖ ^ 2 ≤
          C * ‖fourierTransformR2 f ξ‖ ^ 2) := by sorry

/-- **Integrated bounded overlap on the Fourier side.** Integrating the pointwise
inequality gives $\sum_r \int |\hat{f_r}|^2 \leq C \int |\hat f|^2$. -/
theorem bounded_overlap_fourier
    (f_r : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (scales : Finset ℝ)
    (h_sum : ∀ x, f x = ∑ r ∈ scales, f_r r x)
    (h_support : ∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0) :
    ∃ (C : ℝ), 0 < C ∧
      ∑ r ∈ scales, ∫ ξ, ‖fourierTransformR2 (f_r r) ξ‖ ^ 2 ≤
        C * ∫ ξ, ‖fourierTransformR2 f ξ‖ ^ 2 := by

  obtain ⟨C, hC_pos, h_int_r, h_int_f, h_pw⟩ :=
    bounded_overlap_fourier_pointwise f_r f scales h_sum h_support
  refine ⟨C, hC_pos, ?_⟩

  calc ∑ r ∈ scales, ∫ ξ, ‖fourierTransformR2 (f_r r) ξ‖ ^ 2
      = ∫ ξ, ∑ r ∈ scales, ‖fourierTransformR2 (f_r r) ξ‖ ^ 2 := by
        rw [integral_finset_sum _ (fun r hr => h_int_r r hr)]
    _ ≤ ∫ ξ, C * ‖fourierTransformR2 f ξ‖ ^ 2 := by
        apply integral_mono
        · exact integrable_finset_sum _ (fun r hr => h_int_r r hr)
        · exact h_int_f.const_mul C
        · intro ξ; exact h_pw ξ
    _ = C * ∫ ξ, ‖fourierTransformR2 f ξ‖ ^ 2 := integral_const_mul _ _

/-- **Littlewood–Paley square function estimate.** Combining Plancherel with bounded
overlap on the Fourier side yields the spatial estimate
$\sum_r \int |f_r|^2 \leq C \int |f|^2$. -/
theorem littlewood_paley_square_function
    (f_r : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (scales : Finset ℝ)
    (h_sum : ∀ x, f x = ∑ r ∈ scales, f_r r x)
    (h_support : ∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0) :
    ∃ (C : ℝ), 0 < C ∧
      ∑ r ∈ scales, ∫ x, (f_r r x) ^ 2 ≤ C * ∫ x, (f x) ^ 2 := by

  obtain ⟨C, hC_pos, h_overlap⟩ := bounded_overlap_fourier f_r f scales h_sum h_support
  refine ⟨C, hC_pos, ?_⟩

  have h_lhs : ∑ r ∈ scales, ∫ x, (f_r r x) ^ 2 =
      ∑ r ∈ scales, ∫ ξ, ‖fourierTransformR2 (f_r r) ξ‖ ^ 2 := by
    congr 1; ext r
    exact plancherel_fourierTransformR2 (f_r r)

  have h_rhs : C * ∫ x, (f x) ^ 2 = C * ∫ ξ, ‖fourierTransformR2 f ξ‖ ^ 2 := by
    congr 1
    exact plancherel_fourierTransformR2 f

  rw [h_lhs, h_rhs]
  exact h_overlap

/-- Expanding the $L^2$ norm of a finite sum as a sum of pairwise integrals:
$\int (\sum_i \varphi_i)^2 = \sum_{i,j} \int \varphi_i \varphi_j$. -/
theorem l2_norm_bilinear_expansion
    {ι : Type} [Fintype ι]
    (φ : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ : ∀ i j, Integrable (fun x => φ i x * φ j x) volume) :
    ∫ x, (∑ i : ι, φ i x) ^ 2 =
      ∑ i : ι, ∑ j : ι, ∫ x, φ i x * φ j x := by
  have h_pw : ∀ x, (∑ i : ι, φ i x) ^ 2 = ∑ i : ι, ∑ j : ι, φ i x * φ j x := by
    intro x
    rw [sq, Finset.sum_mul]
    congr 1; ext i; rw [Finset.mul_sum]
  simp_rw [h_pw]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hφ i j))]
  congr 1; ext i
  rw [integral_finset_sum _ (fun j _ => hφ i j)]

/-- Per-tube row sum bound: each row $\sum_j |\langle \varphi_i, \varphi_j\rangle|$ is
controlled by `multiplicity r` (the count of $\varphi_j$ that can interact with
$\varphi_i$) times the diagonal bound $R/r$. -/
theorem tube_inner_product_multiplicity_bound
    (S : TubeCollection) (r : ℝ) (hr_scale : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (hφ_inner_bound : ∀ i j, |∫ x, φ i x * φ j x| ≤ S.R / r)
    (hφ_sparse : ∀ i, (Finset.univ.filter (fun j =>
      (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r) :
    ∀ i : S.ι,
      ∑ j : S.ι, |∫ x, φ i x * φ j x| ≤
        (S.multiplicity r : ℝ) * (S.R / r) := by
  intro i

  have hRr : (0 : ℝ) ≤ S.R / r := by
    apply div_nonneg
    · linarith [S.hR]
    · obtain ⟨k, _, hk1, _⟩ := hr_scale; linarith

  calc ∑ j : S.ι, |∫ x, φ i x * φ j x|
      = ∑ j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
          |∫ x, φ i x * φ j x|
        + ∑ j ∈ Finset.univ.filter (fun j => ¬((∫ x, φ i x * φ j x) ≠ 0)),
          |∫ x, φ i x * φ j x| := by
        rw [Finset.sum_filter_add_sum_filter_not]

    _ = ∑ j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
          |∫ x, φ i x * φ j x| := by
        have h0 : ∑ j ∈ Finset.univ.filter (fun j => ¬((∫ x, φ i x * φ j x) ≠ 0)),
            |∫ x, φ i x * φ j x| = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
          rw [hj, abs_zero]
        linarith

    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0),
          (S.R / r) := by
        apply Finset.sum_le_sum; intro j _; exact hφ_inner_bound i j
    _ = (Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0)).card
          * (S.R / r) := by
        rw [Finset.sum_const, nsmul_eq_mul]

    _ ≤ (S.multiplicity r : ℝ) * (S.R / r) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hφ_sparse i
        · exact hRr

/-- Per-scale $L^2$ bound: given a tube-localized representation
$f_r = \sum_i \varphi_i$ with per-tube energy $\leq R/r$ and bounded multiplicity at
scale $r$, we obtain $\int f_r^2 \leq |S.\iota| \cdot \mathrm{mult}(r) \cdot (R/r)$. -/
theorem per_scale_l2_bound
    (S : TubeCollection) (r : ℝ)
    (hr_scale : r ∈ dyadicScales S.R)
    (f_r : EuclideanSpace ℝ (Fin 2) → ℝ)
    (h_fourier : ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 f_r ξ = 0)
    (h_tube_decomp : ∃ (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ i, Integrable (φ i) volume) ∧
      (∀ i j, Integrable (fun x => φ i x * φ j x) volume) ∧
      (∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) ∧
      (∀ x, f_r x = ∑ i : S.ι, φ i x) ∧
      (∀ i j, |∫ x, φ i x * φ j x| ≤ S.R / r) ∧
      (∀ i, (Finset.univ.filter (fun j =>
        (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r)) :
    ∫ x, (f_r x) ^ 2 ≤
      (Fintype.card S.ι : ℝ) * (S.multiplicity r : ℝ) * (S.R / r) := by

  obtain ⟨φ, _, hφ_prod_int, hφ_freq, hφ_sum, hφ_inner, hφ_sparse⟩ := h_tube_decomp

  have h_expand : ∫ x, (f_r x) ^ 2 = ∑ i : S.ι, ∑ j : S.ι, ∫ x, φ i x * φ j x := by
    conv_lhs => rw [show f_r = fun x => ∑ i : S.ι, φ i x from funext hφ_sum]
    exact l2_norm_bilinear_expansion φ hφ_prod_int


  have h_ortho := tube_inner_product_multiplicity_bound S r hr_scale φ hφ_freq hφ_inner hφ_sparse

  rw [h_expand]
  calc ∑ i : S.ι, ∑ j : S.ι, ∫ x, φ i x * φ j x
      ≤ ∑ i : S.ι, ∑ j : S.ι, |∫ x, φ i x * φ j x| := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact le_abs_self _
    _ = ∑ i : S.ι, (∑ j : S.ι, |∫ x, φ i x * φ j x|) := rfl
    _ ≤ ∑ i : S.ι, ((S.multiplicity r : ℝ) * (S.R / r)) := by
        apply Finset.sum_le_sum; intro i _; exact h_ortho i
    _ = (Fintype.card S.ι : ℝ) * (S.multiplicity r : ℝ) * (S.R / r) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Cauchy–Schwarz via the AM–GM inequality: if $\int f^2, \int g^2 \leq A$ then
$|\int fg| \leq A$. -/
theorem abs_integral_mul_le_of_sq_integral_le
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f g : α → ℝ)
    (hf2_int : Integrable (fun x => (f x) ^ 2) μ)
    (hg2_int : Integrable (fun x => (g x) ^ 2) μ)
    (A : ℝ)
    (hf_bound : ∫ x, (f x) ^ 2 ∂μ ≤ A)
    (hg_bound : ∫ x, (g x) ^ 2 ∂μ ≤ A) :
    |∫ x, f x * g x ∂μ| ≤ A := by

  have h1 : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := by
    have := norm_integral_le_integral_norm (μ := μ) (fun x => f x * g x)
    simp only [Real.norm_eq_abs] at this
    exact this

  have h2 : ∫ x, |f x * g x| ∂μ ≤ ∫ x, ((f x) ^ 2 + (g x) ^ 2) / 2 ∂μ := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun x => abs_nonneg _)
    · exact (hf2_int.add hg2_int).div_const 2
    · apply ae_of_all _; intro x
      simp only
      rw [abs_mul]
      have := two_mul_le_add_sq (|f x|) (|g x|)
      rw [sq_abs, sq_abs] at this
      linarith

  have h3 : ∫ x, ((f x) ^ 2 + (g x) ^ 2) / 2 ∂μ ≤ A := by
    rw [integral_div, integral_add hf2_int hg2_int]
    linarith
  linarith

/-- Existence of a smooth frequency partition: each tube bump $\psi_i$ splits as
$\psi_i = \sum_{r \in \text{scales}} \eta_{r,i}$ where each piece has Fourier support
inside $\{|\xi| \leq 1/r\}$, and similarly for the sum $\sum_i \eta_{r,i}$. -/
theorem smooth_frequency_partition_exists (S : TubeCollection) :
    ∃ (scales : Finset ℝ)
      (η : ℝ → S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),

      (∀ r ∈ scales, r ∈ dyadicScales S.R) ∧

      (∀ i, ∀ x, S.ψ i x = ∑ r ∈ scales, η r i x) ∧

      (∀ r ∈ scales, ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (η r i) ξ = 0) ∧

      (∀ r ∈ scales, ∀ i, Integrable (η r i) volume) ∧

      (∀ r ∈ scales, ∀ i j, Integrable (fun x => η r i x * η r j x) volume) ∧


      (∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (fun x => ∑ i : S.ι, η r i x) ξ = 0) := by sorry

/-- Basic Littlewood–Paley decomposition of the tube sum, together with a tube-wise
representation $f_r = \sum_i \varphi_i$ on each scale. -/
theorem littlewood_paley_lp_decomposition (S : TubeCollection) :
    ∃ (f_r : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
      (scales : Finset ℝ),
      (∀ r ∈ scales, r ∈ dyadicScales S.R) ∧
      (∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x) ∧
      (∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0) ∧
      (∀ r ∈ scales, ∃ (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),
        (∀ i, Integrable (φ i) volume) ∧
        (∀ i j, Integrable (fun x => φ i x * φ j x) volume) ∧
        (∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
          ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) ∧
        (∀ x, f_r r x = ∑ i : S.ι, φ i x)) := by

  obtain ⟨scales, η, h_range, h_partition, h_freq, h_int, h_prod_int, h_sum_freq⟩ :=
    smooth_frequency_partition_exists S

  refine ⟨fun r x => ∑ i : S.ι, η r i x, scales, h_range, ?_, ?_, ?_⟩
  ·

    intro x
    simp only [TubeCollection.tubeSum]
    simp_rw [h_partition]
    rw [Finset.sum_comm]
  ·

    exact h_sum_freq
  ·
    intro r hr
    exact ⟨η r, h_int r hr, h_prod_int r hr, h_freq r hr, fun x => rfl⟩

/-- Per-tube $L^2$ bound at scale $r$: $\int |\varphi_i|^2 \leq R/r$. -/
theorem tube_component_l2_bound (S : TubeCollection) (r : ℝ)
    (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_int : ∀ i, Integrable (φ i) volume)
    (hφ_sq_int : ∀ i, Integrable (fun x => (φ i x) ^ 2) volume)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) :
    ∀ i, ∫ x, (φ i x) ^ 2 ≤ S.R / r := by sorry

/-- Amplitude wrapper: packages the per-tube $L^2$ bound as the existence of
nonnegative dominating functions $g_i \geq \varphi_i^2$ with $\int g_i \leq R/r$. -/
theorem littlewood_paley_tube_amplitude (S : TubeCollection) (r : ℝ)
    (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_int : ∀ i, Integrable (φ i) volume)
    (hφ_sq_int : ∀ i, Integrable (fun x => (φ i x) ^ 2) volume)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) :
    ∃ (g : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ i, Integrable (g i) volume) ∧
      (∀ i, ∀ x, (φ i x) ^ 2 ≤ g i x) ∧
      (∀ i, ∫ x, g i x ≤ S.R / r) := by

  refine ⟨fun i x => (φ i x) ^ 2, ?_, fun i x => le_refl _, ?_⟩

  · exact hφ_sq_int

  · exact tube_component_l2_bound S r hr φ hφ_int hφ_sq_int hφ_freq

/-- Recover a per-tube $L^2$ bound $\int \varphi_i^2 \leq R/r$ from a pointwise
domination by integrable amplitudes $g_i$ with $\int g_i \leq R/r$. -/
theorem self_norm_from_amplitude
    {ι : Type} [Fintype ι]
    (φ : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (R r : ℝ)
    (hφ_sq_int : ∀ i, Integrable (fun x => (φ i x) ^ 2) volume)
    (g : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg_int : ∀ i, Integrable (g i) volume)
    (h_pw : ∀ i, ∀ x, (φ i x) ^ 2 ≤ g i x)
    (h_integral_bound : ∀ i, ∫ x, g i x ≤ R / r) :
    ∀ i, ∫ x, (φ i x) ^ 2 ≤ R / r := by
  intro i
  calc ∫ x, (φ i x) ^ 2 ≤ ∫ x, g i x := by
        apply integral_mono (hφ_sq_int i) (hg_int i)
        intro x; exact h_pw i x
    _ ≤ R / r := h_integral_bound i

/-- Angular Fourier disjointness: if the directions of tubes $i, j$ make a large enough
angle (so $|\langle d_i, d_j\rangle| < 1 - (r/R)^2/2$), then the Fourier supports of
their pieces $\varphi_i$ and $\varphi_j$ are disjoint. -/
theorem angular_fourier_disjoint_support (S : TubeCollection) (r : ℝ)
    (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (i j : S.ι)
    (h_angle : |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| < 1 - (r / S.R) ^ 2 / 2)
    (ξ : EuclideanSpace ℝ (Fin 2))
    (hξ : fourierTransformR2 (φ i) ξ ≠ 0) :
    fourierTransformR2 (φ j) ξ = 0 := by sorry

/-- Refined Littlewood–Paley construction including per-tube $L^2$ bounds and angular
Fourier disjointness for non-aligned tubes. -/
theorem littlewood_paley_fourier_construction (S : TubeCollection) :
    ∃ (f_r : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
      (scales : Finset ℝ),
      (∀ r ∈ scales, r ∈ dyadicScales S.R) ∧
      (∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x) ∧
      (∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0) ∧
      (∀ r ∈ scales, ∃ (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),
        (∀ i, Integrable (φ i) volume) ∧
        (∀ i j, Integrable (fun x => φ i x * φ j x) volume) ∧
        (∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
          ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) ∧
        (∀ x, f_r r x = ∑ i : S.ι, φ i x) ∧
        (∀ i, ∫ x, (φ i x) ^ 2 ≤ S.R / r) ∧
        (∀ i j, |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| <
            1 - (r / S.R) ^ 2 / 2 →
          ∀ ξ : EuclideanSpace ℝ (Fin 2),
            fourierTransformR2 (φ i) ξ ≠ 0 → fourierTransformR2 (φ j) ξ = 0)) := by

  obtain ⟨f_r, scales, h_range, h_sum, h_fourier, h_decomp⟩ :=
    littlewood_paley_lp_decomposition S
  refine ⟨f_r, scales, h_range, h_sum, h_fourier, ?_⟩
  intro r hr

  obtain ⟨φ, hφ_int, hφ_prod_int, hφ_freq, hφ_sum⟩ := h_decomp r hr
  refine ⟨φ, hφ_int, hφ_prod_int, hφ_freq, hφ_sum, ?_, fun i j h_ang ξ hξ =>
    angular_fourier_disjoint_support S r (h_range r hr) φ hφ_freq i j h_ang ξ hξ⟩

  have hφ_sq_int : ∀ i, Integrable (fun x => (φ i x) ^ 2) volume := by
    intro i; have := hφ_prod_int i i; simp only [← sq] at this; exact this
  obtain ⟨g, hg_int, h_pw, h_g_bound⟩ :=
    littlewood_paley_tube_amplitude S r (h_range r hr) φ hφ_int hφ_sq_int hφ_freq

  exact self_norm_from_amplitude φ S.R r hφ_sq_int g hg_int h_pw h_g_bound

/-- Spatial orthogonality from Fourier-side disjointness: when the angle between tubes
$i, j$ is large, $\int \varphi_i \varphi_j = 0$ via Plancherel and disjoint supports. -/
theorem freq_orthogonality_of_large_angle (S : TubeCollection) (r : ℝ) (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (hφ_int : ∀ i j, Integrable (fun x => φ i x * φ j x) volume)
    (hφ_disjoint_support : ∀ i j, |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| <
        1 - (r / S.R) ^ 2 / 2 →
      ∀ ξ : EuclideanSpace ℝ (Fin 2),
        fourierTransformR2 (φ i) ξ ≠ 0 → fourierTransformR2 (φ j) ξ = 0)
    (i j : S.ι)
    (h_angle : |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| < 1 - (r / S.R) ^ 2 / 2) :
    ∫ x, φ i x * φ j x = 0 := by

  rw [plancherel_bilinear_fourierTransformR2 (φ i) (φ j)]

  have h_zero : ∀ ξ : EuclideanSpace ℝ (Fin 2),
      (fourierTransformR2 (φ i) ξ * starRingEnd ℂ (fourierTransformR2 (φ j) ξ)).re = 0 := by
    intro ξ
    by_cases hi : fourierTransformR2 (φ i) ξ = 0
    · simp [hi]
    · have hj := hφ_disjoint_support i j h_angle ξ hi
      simp [hj]

  simp_rw [h_zero]
  simp

/-- Spatial decay vanishing: when the tubes $i, j$ are nearly parallel but tube $j$ is
not contained in the $r \times R$ rectangle around tube $i$, the interaction integral
$\int \varphi_i \varphi_j = 0$. -/
theorem spatial_decay_integral_vanishing (S : TubeCollection) (r : ℝ) (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (hφ_int : ∀ i j, Integrable (fun x => φ i x * φ j x) volume)
    (i j : S.ι)
    (h_angle : |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| ≥ 1 - (r / S.R) ^ 2 / 2)
    (h_not_contained : ¬((S.tubes j).asSet ⊆ rectangleSet (S.tubes i).center (S.tubes i).direction r S.R)) :
    ∫ x, φ i x * φ j x = 0 := by sorry

/-- Contrapositive of spatial decay: if the interaction $\int \varphi_i \varphi_j$ is
nonzero and the tubes are nearly parallel, then tube $j$ must be contained in the
$r \times R$ rectangle centred at tube $i$. -/
theorem tube_containment_of_nonzero_integral (S : TubeCollection) (r : ℝ) (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (hφ_int : ∀ i j, Integrable (fun x => φ i x * φ j x) volume)
    (i j : S.ι)
    (h_angle : |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| ≥ 1 - (r / S.R) ^ 2 / 2)
    (h_nonzero : (∫ x, φ i x * φ j x) ≠ 0) :
    (S.tubes j).asSet ⊆ rectangleSet (S.tubes i).center (S.tubes i).direction r S.R := by


  by_contra h_not_contained
  exact absurd (spatial_decay_integral_vanishing S r hr φ hφ_freq hφ_int i j h_angle h_not_contained)
    h_nonzero

/-- Frequency-localization of nonzero interactions: for each tube $i$ there is a
rectangle (centred at the tube) outside of which every tube $j$ has zero interaction
with $\varphi_i$. -/
theorem tube_freq_loc_vanishing (S : TubeCollection) (r : ℝ) (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (hφ_int : ∀ i j, Integrable (fun x => φ i x * φ j x) volume)
    (hφ_disjoint_support : ∀ i j, |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| <
        1 - (r / S.R) ^ 2 / 2 →
      ∀ ξ : EuclideanSpace ℝ (Fin 2),
        fourierTransformR2 (φ i) ξ ≠ 0 → fourierTransformR2 (φ j) ξ = 0) :
    ∀ i, ∃ (c : EuclideanSpace ℝ (Fin 2)) (d : EuclideanSpace ℝ (Fin 2)),
      ∀ j, (∫ x, φ i x * φ j x) ≠ 0 →
        (S.tubes j).asSet ⊆ rectangleSet c d r S.R := by
  intro i

  refine ⟨(S.tubes i).center, (S.tubes i).direction, ?_⟩
  intro j hj

  by_cases h_angle : |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| <
      1 - (r / S.R) ^ 2 / 2
  ·
    exact absurd (freq_orthogonality_of_large_angle S r hr φ hφ_freq hφ_int
      hφ_disjoint_support i j h_angle) hj
  ·
    exact tube_containment_of_nonzero_integral S r hr φ hφ_freq hφ_int i j
      (not_lt.mp h_angle) hj

/-- Sparsity bound from orthogonality: for each tube $i$, the number of $j$ with
$\int \varphi_i \varphi_j \ne 0$ is at most $\mathrm{mult}(r)$, the maximum tube
multiplicity inside any $r \times R$ rectangle. -/
theorem sparsity_from_orthogonality (S : TubeCollection) (r : ℝ) (hr : r ∈ dyadicScales S.R)
    (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ_freq : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0)
    (hφ_int : ∀ i j, Integrable (fun x => φ i x * φ j x) volume)
    (hφ_disjoint_support : ∀ i j, |⟪(S.tubes i).direction, (S.tubes j).direction⟫_ℝ| <
        1 - (r / S.R) ^ 2 / 2 →
      ∀ ξ : EuclideanSpace ℝ (Fin 2),
        fourierTransformR2 (φ i) ξ ≠ 0 → fourierTransformR2 (φ j) ξ = 0) :
    ∀ i, (Finset.univ.filter (fun j =>
      (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r := by
  intro i

  obtain ⟨c, d, h_vanish⟩ := tube_freq_loc_vanishing S r hr φ hφ_freq hφ_int
    hφ_disjoint_support i


  have h_sub : Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0) ⊆
      Finset.univ.filter (fun j => (S.tubes j).asSet ⊆ rectangleSet c d r S.R) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact h_vanish j hj

  have h_card : (Finset.univ.filter (fun j => (∫ x, φ i x * φ j x) ≠ 0)).card ≤
      S.countContained r c d :=
    Finset.card_le_card h_sub

  have h_le_mult : S.countContained r c d ≤ S.multiplicity r := by
    apply le_csSup
    ·
      use Fintype.card S.ι
      intro n hn
      obtain ⟨c', d', hn_eq⟩ := hn
      rw [hn_eq]
      unfold TubeCollection.countContained
      exact Finset.card_filter_le _ _
    · exact ⟨c, d, rfl⟩
  linarith

/-- Full Littlewood–Paley construction packaging together: tube decomposition, per-tube
$L^2$ bounds, and sparsity of nonzero pairwise interactions. -/
theorem littlewood_paley_construction (S : TubeCollection) :
    ∃ (f_r : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
      (scales : Finset ℝ),
      (∀ r ∈ scales, r ∈ dyadicScales S.R) ∧
      (∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x) ∧
      (∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0) ∧
      (∀ r ∈ scales, ∃ (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),
        (∀ i, Integrable (φ i) volume) ∧
        (∀ i j, Integrable (fun x => φ i x * φ j x) volume) ∧
        (∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
          ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) ∧
        (∀ x, f_r r x = ∑ i : S.ι, φ i x) ∧
        (∀ i, ∫ x, (φ i x) ^ 2 ≤ S.R / r) ∧
        (∀ i, (Finset.univ.filter (fun j =>
          (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r)) := by

  obtain ⟨f_r, scales, h_range, h_sum, h_fourier, h_decomp⟩ :=
    littlewood_paley_fourier_construction S
  refine ⟨f_r, scales, h_range, h_sum, h_fourier, ?_⟩
  intro r hr
  obtain ⟨φ, hφ_int, hφ_prod_int, hφ_freq, hφ_sum, hφ_self_norm, hφ_disjoint⟩ := h_decomp r hr
  refine ⟨φ, hφ_int, hφ_prod_int, hφ_freq, hφ_sum, hφ_self_norm, ?_⟩

  exact sparsity_from_orthogonality S r (h_range r hr) φ hφ_freq hφ_prod_int hφ_disjoint

/-- The final tube decomposition: each scale piece $f_r = \sum_i \varphi_i$ has
absolutely bounded pairwise interactions $|\int \varphi_i \varphi_j| \leq R/r$
(by Cauchy–Schwarz) and bounded multiplicity. -/
theorem littlewood_paley_tube_decomposition (S : TubeCollection) :
    ∃ (f_r : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
      (scales : Finset ℝ),
      (∀ r ∈ scales, r ∈ dyadicScales S.R) ∧
      (∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x) ∧
      (∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
        ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0) ∧
      (∀ r ∈ scales, ∃ (φ : S.ι → EuclideanSpace ℝ (Fin 2) → ℝ),
        (∀ i, Integrable (φ i) volume) ∧
        (∀ i j, Integrable (fun x => φ i x * φ j x) volume) ∧
        (∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
          ‖ξ‖ > 1 / r → fourierTransformR2 (φ i) ξ = 0) ∧
        (∀ x, f_r r x = ∑ i : S.ι, φ i x) ∧
        (∀ i j, |∫ x, φ i x * φ j x| ≤ S.R / r) ∧
        (∀ i, (Finset.univ.filter (fun j =>
          (∫ x, φ i x * φ j x) ≠ 0)).card ≤ S.multiplicity r)) := by

  obtain ⟨f_r, scales, h_range, h_sum, h_fourier, h_tube_decomp⟩ :=
    littlewood_paley_construction S
  refine ⟨f_r, scales, h_range, h_sum, h_fourier, ?_⟩
  intro r hr
  obtain ⟨φ, hφ_int, hφ_prod_int, hφ_freq, hφ_sum, hφ_self_norm, hφ_sparse⟩ :=
    h_tube_decomp r hr
  refine ⟨φ, hφ_int, hφ_prod_int, hφ_freq, hφ_sum, ?_, hφ_sparse⟩

  intro i j
  have hf2 : Integrable (fun x => (φ i x) ^ 2) volume := by
    have := hφ_prod_int i i
    simp only [← sq] at this
    exact this
  have hg2 : Integrable (fun x => (φ j x) ^ 2) volume := by
    have := hφ_prod_int j j
    simp only [← sq] at this
    exact this
  exact abs_integral_mul_le_of_sq_integral_le (φ i) (φ j) hf2 hg2 (S.R / r)
    (hφ_self_norm i) (hφ_self_norm j)

/-- **Main Lemma 2R** (real Fourier method, $1 \times R$ tubes). Let $\mathcal{T}$ be a
set of $1 \times R$ tubes in $\mathbb{R}^2$ and $f = \sum_T \psi_T$ the associated tube
sum. There exists a frequency decomposition $f = \sum_{r \in \text{scales}} f_r$ into
dyadic pieces, with $\hat{f_r}$ supported in $\{|\xi| \leq 1/r\}$, near-orthogonality
$\sum_r \int f_r^2 \lesssim \int f^2$, and the per-scale estimate
$\int f_r^2 \leq C \cdot |\mathcal{T}| \cdot \mathrm{mult}(r) \cdot (R/r)$. -/
theorem main_lemma_2R
    (S : TubeCollection) :
    ∃ (D : FrequencyDecomposition S) (C : ℝ), 0 < C ∧
      ∀ r ∈ D.scales,
        ∫ x, (D.f_r r x) ^ 2 ≤
          C * (Fintype.card S.ι : ℝ) * (S.multiplicity r : ℝ) * (S.R / r) := by

  obtain ⟨f_r, scales, h_range, h_sum, h_fourier, h_tube_decomp⟩ :=
    littlewood_paley_tube_decomposition S

  obtain ⟨C_orth, hC_orth_pos, h_orth⟩ :=
    littlewood_paley_square_function f_r S.tubeSum scales h_sum h_fourier

  let D : FrequencyDecomposition S := {
    f_r := f_r
    scales := scales
    scales_range := h_range
    sum_eq := h_sum
    fourier_support := h_fourier
    near_orthogonality := ⟨C_orth, hC_orth_pos, h_orth⟩
  }

  refine ⟨D, 1, one_pos, ?_⟩
  intro r hr
  simp only [D, one_mul]
  exact per_scale_l2_bound S r (h_range r hr) (f_r r) (h_fourier r hr) (h_tube_decomp r hr)

end ProjectionTheory

end
