/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory Metric Set

noncomputable section

namespace FrequencyDecomposition

/-- Short alias for the Euclidean plane $\mathbb{R}^2$. -/
abbrev ℝ2 := EuclideanSpace ℝ (Fin 2)

/-- A $1 \times R$ tube in $\mathbb{R}^2$: an oriented rectangle of length $R \geq 1$
and width $1$, specified by its center and direction angle. -/
structure Tube where
  center : ℝ2
  direction : ℝ
  R : ℝ
  hR : 1 ≤ R

/-- A generic axis-aligned-along-direction rectangle in $\mathbb{R}^2$, with arbitrary
`halfWidth` and `halfLength`, used to contain bundles of $1 \times R$ tubes. -/
structure WideTube where
  center : ℝ2
  direction : ℝ
  halfWidth : ℝ
  halfLength : ℝ

/-- Realize a tube $T$ as the rectangle of half-length $R/2$ along direction $\theta$
and half-width $1/2$ along the perpendicular. -/
def Tube.toSet (T : Tube) : Set ℝ2 :=
  {x | let diff := (EuclideanSpace.equiv (Fin 2) ℝ) (x - T.center)
       let θ := T.direction
       let longCoord := diff 0 * Real.cos θ + diff 1 * Real.sin θ
       let shortCoord := -diff 0 * Real.sin θ + diff 1 * Real.cos θ
       |longCoord| ≤ T.R / 2 ∧ |shortCoord| ≤ 1 / 2}

/-- Realize a `WideTube` as the corresponding rectangle in $\mathbb{R}^2$. -/
def WideTube.toSet (W : WideTube) : Set ℝ2 :=
  {x | let diff := (EuclideanSpace.equiv (Fin 2) ℝ) (x - W.center)
       let θ := W.direction
       let longCoord := diff 0 * Real.cos θ + diff 1 * Real.sin θ
       let shortCoord := -diff 0 * Real.sin θ + diff 1 * Real.cos θ
       |longCoord| ≤ W.halfLength ∧ |shortCoord| ≤ W.halfWidth}

/-- A tube $T$ is contained in a wide tube $W$ if the rectangle of $T$ lies inside $W$. -/
def Tube.containedIn (T : Tube) (W : WideTube) : Prop :=
  T.toSet ⊆ W.toSet

/-- The dyadic scales up to $R$: $\{2^k : k \in \mathbb{N}, 2^k \leq R\}$ as a `Finset`. -/
def dyadicRange (R : ℝ) : Finset ℝ :=
  ((Finset.range (Nat.log 2 ⌊R⌋₊ + 1)).image (fun k => (2 : ℝ) ^ k)).filter (· ≤ R)

open Classical in
/-- Tube covering number $N_\mathcal{T}(r) = \max_W |\{T \in \mathcal{T} : T \subseteq W\}|$,
maximizing over $r \times R$ wide tubes $W$. -/
def tubeCoveringNumber (𝒯 : Finset Tube) (R r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
    n = (𝒯.filter (fun T => T.containedIn W)).card}

/-- The $L^2$ norm squared $\|f\|_{L^2}^2 = \int_{\mathbb{R}^2} |f(x)|^2\, dx$. -/
def l2NormSq (f : ℝ2 → ℂ) : ℝ :=
  ∫ x, ‖f x‖ ^ 2

/-- The support of the Fourier transform of `f` in $\mathbb{R}^2$. -/
def fourierSupport (f : ℝ2 → ℂ) : Set ℝ2 :=
  Function.support (FourierTransform.fourier f)

/-- The cumulative frequency projection $P_{\leq 1/r} f$: the inverse Fourier transform
of $\hat f(\xi) \cdot \mathbf{1}_{|\xi| \leq 1/r}$. -/
def cumulativeFreqProj (f : ℝ2 → ℂ) (r : ℝ) : ℝ2 → ℂ :=
  FourierTransformInv.fourierInv
    (fun ξ => (FourierTransform.fourier f) ξ * (if dist ξ 0 ≤ 1 / r then (1 : ℂ) else 0))

/-- The $k$-th Littlewood–Paley piece of $f$ at depth $K$:
$\Delta_k f = P_{\leq 2^{-k}} f - P_{\leq 2^{-(k+1)}} f$ for $k < K$, and the final
endpoint $P_{\leq 2^{-K}} f$ when $k = K$ (with $f$ itself when $k = 0$). -/
def littlewoodPaleyPieceK (f : ℝ2 → ℂ) (K k : ℕ) (x : ℝ2) : ℂ :=
  let g : ℕ → ℂ := fun j => if j = 0 then f x else cumulativeFreqProj f ((2 : ℝ) ^ j) x
  if k < K then g k - g (k + 1) else g K

/-- Littlewood–Paley telescoping identity: $f(x) = \sum_{k=0}^{K} \Delta_k f(x)$. -/
theorem littlewoodPaleyPieceK_sum (f : ℝ2 → ℂ) (K : ℕ) (x : ℝ2) :
    ∑ k ∈ Finset.range (K + 1), littlewoodPaleyPieceK f K k x = f x := by
  simp only [littlewoodPaleyPieceK]
  set g : ℕ → ℂ := fun j => if j = 0 then f x else cumulativeFreqProj f ((2 : ℝ) ^ j) x
  rw [Finset.sum_range_succ]
  simp only [show ¬ (K < K) from lt_irrefl K, ite_false]
  rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
  rw [show (fun k => g k - g (k + 1)) = (fun k => -(g (k + 1) - g k)) from by ext; ring]
  rw [Finset.sum_neg_distrib, Finset.sum_range_sub]
  simp only [g, if_true]; ring

/-- The natural logarithm base 2 of $\lfloor 2^k \rfloor$ equals $k$. -/
lemma nat_log_two_pow (k : ℕ) : Nat.log 2 ⌊((2 : ℝ) ^ k)⌋₊ = k := by
  rw [show ((2:ℝ) ^ k) = ((2:ℕ) ^ k : ℕ) from by push_cast; ring, Nat.floor_natCast]
  exact Nat.log_pow (by norm_num : 1 < 2) k

/-- If $k \leq \log_2 \lfloor R \rfloor$ then $2^k \leq R$. -/
lemma two_pow_le_of_mem_range (k : ℕ) (R : ℝ) (hR : 1 ≤ R) (hk : k < Nat.log 2 ⌊R⌋₊ + 1) :
    (2:ℝ) ^ k ≤ R := by
  have hk' : k ≤ Nat.log 2 ⌊R⌋₊ := Nat.lt_succ_iff.mp hk
  have hne : ⌊R⌋₊ ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.floor_pos.mpr hR)
  have h2k : (2:ℕ) ^ k ≤ ⌊R⌋₊ :=
    (Nat.pow_le_pow_right (by norm_num) hk').trans (Nat.pow_log_le_self 2 hne)
  calc (2:ℝ) ^ k = ((2:ℕ)^k : ℕ) := by push_cast; ring
    _ ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast h2k
    _ ≤ R := Nat.floor_le (by linarith)

/-- Injectivity of $k \mapsto 2^k$ on $\mathbb{N}$ (viewed in $\mathbb{R}$). -/
lemma two_pow_injective : Function.Injective (fun k : ℕ => (2:ℝ) ^ k) := by
  intro a b h
  have h2 : ((2:ℕ)^a : ℝ) = ((2:ℕ)^b : ℝ) := by push_cast; exact h
  exact Nat.pow_right_injective (by norm_num : 2 ≥ 2) (by exact_mod_cast h2)

/-- The Littlewood–Paley piece $f_r$ at dyadic scale $r$ of the tube sum
$f = \sum_T \varphi_T$, indexed by the integer $\log_2 r$. -/
def littlewoodPaleyPiece (𝒯 : Finset Tube) (φ : Tube → ℝ2 → ℂ) (R r : ℝ) : ℝ2 → ℂ :=
  let f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  fun x => littlewoodPaleyPieceK f (Nat.log 2 ⌊R⌋₊) (Nat.log 2 ⌊r⌋₊) x

/-- Bundle of frequency-decomposition data for the tube sum $f = \sum_T \varphi_T$:
the pieces $f_r$ at dyadic scales, Fourier support inside $\{|\xi| \leq 1/r\}$, and
the per-scale $L^2$ estimate $\|f_r\|_{L^2}^2 \leq C \cdot N_\mathcal{T}(r) \cdot
|\mathcal{T}| / r \cdot R$. -/
structure FrequencyDecompositionData (𝒯 : Finset Tube) (R : ℝ) where
  φ : Tube → ℝ2 → ℂ
  f_r : ℝ → ℝ2 → ℂ
  f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  decomposition : ∀ x, f x = ∑ r ∈ dyadicRange R, f_r r x
  freq_support : ∀ r ∈ dyadicRange R,
    fourierSupport (f_r r) ⊆ Metric.closedBall 0 (1 / r)
  C : ℝ
  hC : 0 < C
  l2_estimate : ∀ r ∈ dyadicRange R,
    l2NormSq (f_r r) ≤ C * (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * r⁻¹ * R

/-- The tube sum reconstructs from its Littlewood–Paley pieces:
$\sum_{T \in \mathcal{T}} \varphi_T(x) = \sum_{r \in \text{dyadicRange}(R)} f_r(x)$. -/
theorem littlewoodPaley_decomposition
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet) :
    ∀ x, (fun x => ∑ T ∈ 𝒯, φ T x) x =
      ∑ r ∈ dyadicRange R, littlewoodPaleyPiece 𝒯 φ R r x := by
  intro x
  set f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  rw [show f x = ∑ k ∈ Finset.range (Nat.log 2 ⌊R⌋₊ + 1),
      littlewoodPaleyPieceK f (Nat.log 2 ⌊R⌋₊) k x
    from (littlewoodPaleyPieceK_sum f (Nat.log 2 ⌊R⌋₊) x).symm]
  simp only [littlewoodPaleyPiece, dyadicRange]
  rw [Finset.sum_filter, Finset.sum_image (fun k₁ _ k₂ _ h => two_pow_injective h)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [two_pow_le_of_mem_range k R hR (Finset.mem_range.mp hk), ite_true, nat_log_two_pow]
  rfl

/-- Fourier inversion: $\mathcal{F}(\mathcal{F}^{-1}g) = g$. -/
theorem fourier_fourierInv
    (g : ℝ2 → ℂ) :
    FourierTransform.fourier (FourierTransformInv.fourierInv g) = g := by sorry

/-- Linearity of the inverse Fourier transform under subtraction:
$\mathcal{F}^{-1}g_1 - \mathcal{F}^{-1}g_2 = \mathcal{F}^{-1}(g_1 - g_2)$. -/
theorem fourierInv_sub'
    (g₁ g₂ : ℝ2 → ℂ) :
    (fun x => FourierTransformInv.fourierInv g₁ x - FourierTransformInv.fourierInv g₂ x) =
      FourierTransformInv.fourierInv (g₁ - g₂) := by sorry

/-- Endpoint case ($k \geq K$ or $k = 0$): the Littlewood–Paley piece can be written as
the inverse Fourier transform of a function supported in the ball of radius $1/2^k$. -/
theorem lp_piece_endpoint_as_fourierInv
    (f : ℝ2 → ℂ) (K k : ℕ) (hk : ¬(k < K) ∨ k = 0) :
    ∃ g : ℝ2 → ℂ, Function.support g ⊆ Metric.closedBall 0 (1 / (2:ℝ) ^ k) ∧
      (fun x => littlewoodPaleyPieceK f K k x) = FourierTransformInv.fourierInv g := by sorry

/-- The annular difference $\hat f \cdot (\mathbf 1_{B_{1/2^k}} - \mathbf 1_{B_{1/2^{k+1}}})$
is supported in the ball of radius $1/2^k$. -/
lemma annular_support_in_ball (f : ℝ2 → ℂ) (k : ℕ) :
    Function.support (fun ξ => (FourierTransform.fourier f) ξ *
      (if dist ξ 0 ≤ 1 / (2:ℝ) ^ k then (1:ℂ) else 0) -
      (FourierTransform.fourier f) ξ *
      (if dist ξ 0 ≤ 1 / (2:ℝ) ^ (k+1) then (1:ℂ) else 0)) ⊆
      Metric.closedBall 0 (1 / (2:ℝ) ^ k) := by
  intro ξ hξ
  simp only [Function.mem_support] at hξ
  rw [Metric.mem_closedBall]
  by_contra h
  push_neg at h
  have h' : dist ξ 0 > 1 / (2:ℝ) ^ k := by linarith [dist_comm (0 : ℝ2) ξ]
  have h1 : ¬ (dist ξ 0 ≤ 1 / (2:ℝ) ^ k) := not_le.mpr h'
  have h2 : ¬ (dist ξ 0 ≤ 1 / (2:ℝ) ^ (k+1)) := by
    apply not_le.mpr
    have hpow : (2:ℝ) ^ k ≤ (2:ℝ) ^ (k+1) := by gcongr <;> [norm_num; omega]
    have := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1).le (by positivity) hpow
    linarith
  simp only [h1, h2, ite_false, mul_zero, sub_self] at hξ
  exact hξ rfl

/-- Every Littlewood–Paley piece is the inverse Fourier transform of some function
supported in the ball of radius $1/2^k$, regardless of whether the piece is interior
or an endpoint. -/
theorem lp_piece_as_fourierInv
    (f : ℝ2 → ℂ) (K k : ℕ) :
    ∃ g : ℝ2 → ℂ, Function.support g ⊆ Metric.closedBall 0 (1 / (2:ℝ) ^ k) ∧
      (fun x => littlewoodPaleyPieceK f K k x) = FourierTransformInv.fourierInv g := by
  by_cases hkK : k < K
  · by_cases hk0 : k = 0
    · exact lp_piece_endpoint_as_fourierInv f K k (Or.inr hk0)
    ·
      set h₁ : ℝ2 → ℂ := fun ξ => (FourierTransform.fourier f) ξ *
        (if dist ξ 0 ≤ 1 / (2:ℝ) ^ k then (1:ℂ) else 0)
      set h₂ : ℝ2 → ℂ := fun ξ => (FourierTransform.fourier f) ξ *
        (if dist ξ 0 ≤ 1 / (2:ℝ) ^ (k+1) then (1:ℂ) else 0)
      refine ⟨h₁ - h₂, annular_support_in_ball f k, ?_⟩
      have heq : (fun x => littlewoodPaleyPieceK f K k x) =
          (fun x => FourierTransformInv.fourierInv h₁ x -
            FourierTransformInv.fourierInv h₂ x) := by
        ext x
        simp only [littlewoodPaleyPieceK, hkK, ite_true]
        simp only [show k ≠ 0 from hk0, ite_false,
          show k + 1 ≠ 0 from Nat.succ_ne_zero k, ite_false]
        rfl
      rw [heq, fourierInv_sub']
  · exact lp_piece_endpoint_as_fourierInv f K k (Or.inl hkK)

/-- The Fourier transform of the $k$-th Littlewood–Paley piece is supported in
the ball of radius $1/2^k$. -/
theorem fourier_lp_piece_support
    (f : ℝ2 → ℂ) (K k : ℕ) :
    fourierSupport (fun x => littlewoodPaleyPieceK f K k x) ⊆
      Metric.closedBall 0 (1 / (2 : ℝ) ^ k) := by
  obtain ⟨g, hsupp, heq⟩ := lp_piece_as_fourierInv f K k
  rw [show (fun x => littlewoodPaleyPieceK f K k x) = FourierTransformInv.fourierInv g from heq]
  intro ξ hξ
  simp only [fourierSupport, Function.mem_support] at hξ
  rw [congr_fun (fourier_fourierInv g) ξ] at hξ
  exact hsupp hξ

/-- Frequency support of each Littlewood–Paley piece $f_r$ lies in the ball
$\{|\xi| \leq 1/r\}$. -/
theorem littlewoodPaley_freq_support
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet) :
    ∀ r ∈ dyadicRange R,
      fourierSupport (littlewoodPaleyPiece 𝒯 φ R r) ⊆ Metric.closedBall 0 (1 / r) := by
  intro r hr
  simp only [dyadicRange, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨⟨k, _, hk_eq⟩, _⟩ := hr
  subst hk_eq
  simp only [littlewoodPaleyPiece, nat_log_two_pow]
  exact fourier_lp_piece_support _ _ k

/-- Every element of `dyadicRange R` is strictly positive (it is a power of $2$). -/
lemma pos_of_mem_dyadicRange {R r : ℝ} (hr : r ∈ dyadicRange R) : 0 < r := by
  simp only [dyadicRange, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨⟨k, _, hk⟩, _⟩ := hr
  rw [← hk]; positivity

/-- **Plancherel for the inverse Fourier transform** on $\mathbb{R}^2$:
$\int |\mathcal{F}^{-1}g|^2 = \int |g|^2$ whenever the LHS is integrable. -/
theorem plancherel_fourierInv
    (g : ℝ2 → ℂ)
    (hg : Integrable (fun x => ‖FourierTransformInv.fourierInv g x‖ ^ 2) volume) :
    ∫ x, ‖FourierTransformInv.fourierInv g x‖ ^ 2 = ∫ ξ, ‖g ξ‖ ^ 2 := by sorry

/-- Core frequency-side estimate: if $\varphi$ is a smooth integrable function
supported in a $1 \times R$ tube $T$, then the $L^2$ mass of its Fourier transform
restricted to the ball $\{|\xi| \leq 1/r\}$ is at most $R/r$. -/
theorem tube_freq_restricted_l2_bound_core
    (φ : ℝ2 → ℂ) (hsmooth : ContDiff ℝ ⊤ φ) (hint : Integrable φ volume)
    (T : Tube) (hsupp : Function.support φ ⊆ T.toSet)
    (R : ℝ) (hR : 1 ≤ R) (hTR : T.R = R)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R) :
    ∫ ξ, ‖(FourierTransform.fourier φ) ξ *
      (if dist ξ 0 ≤ 1 / r then (1 : ℂ) else 0)‖ ^ 2 ≤ r⁻¹ * R := by sorry

/-- $|P_{\leq 1/r}\varphi|^2$ is integrable on $\mathbb{R}^2$, where $\varphi$ is a
smooth integrable tube-supported function. -/
theorem tube_freq_loc_spatial_integrable
    (φ : ℝ2 → ℂ) (hsmooth : ContDiff ℝ ⊤ φ) (hint : Integrable φ volume)
    (T : Tube) (hsupp : Function.support φ ⊆ T.toSet)
    (R : ℝ) (hR : 1 ≤ R) (hTR : T.R = R)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R) :
    Integrable (fun x => ‖cumulativeFreqProj φ r x‖ ^ 2) volume := by sorry

/-- Spatial $L^2$ bound for the frequency-localized tube function:
$\|P_{\leq 1/r}\varphi\|_{L^2}^2 \leq R/r$. Follows from the core frequency bound
via Plancherel. -/
theorem tube_freq_loc_spatial_l2_bound
    (φ : ℝ2 → ℂ) (hsmooth : ContDiff ℝ ⊤ φ) (hint : Integrable φ volume)
    (T : Tube) (hsupp : Function.support φ ⊆ T.toSet)
    (R : ℝ) (hR : 1 ≤ R) (hTR : T.R = R)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R) :
    ∫ x, ‖cumulativeFreqProj φ r x‖ ^ 2 ≤ r⁻¹ * R := by
  have hint2 := tube_freq_loc_spatial_integrable φ hsmooth hint T hsupp R hR hTR r hr_pos hr_le
  simp only [cumulativeFreqProj] at hint2 ⊢
  rw [plancherel_fourierInv _ hint2]
  exact tube_freq_restricted_l2_bound_core φ hsmooth hint T hsupp R hR hTR r hr_pos hr_le

/-- Equivalent frequency-side statement: $\int |\hat\varphi(\xi)|^2
\mathbf 1_{|\xi| \leq 1/r}\, d\xi \leq R/r$. -/
theorem tube_fourier_restricted_l2_bound
    (φ : ℝ2 → ℂ) (hsmooth : ContDiff ℝ ⊤ φ) (hint : Integrable φ volume)
    (T : Tube) (hsupp : Function.support φ ⊆ T.toSet)
    (R : ℝ) (hR : 1 ≤ R) (hTR : T.R = R)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R) :
    ∫ ξ, ‖(FourierTransform.fourier φ) ξ *
      (if dist ξ 0 ≤ 1 / r then (1 : ℂ) else 0)‖ ^ 2 ≤ r⁻¹ * R := by


  have hint2 := tube_freq_loc_spatial_integrable φ hsmooth hint T hsupp R hR hTR r hr_pos hr_le
  have hplanch := plancherel_fourierInv
    (fun ξ => (FourierTransform.fourier φ) ξ * (if dist ξ 0 ≤ 1 / r then (1 : ℂ) else 0))
    hint2


  rw [← hplanch]
  exact tube_freq_loc_spatial_l2_bound φ hsmooth hint T hsupp R hR hTR r hr_pos hr_le

/-- Plancherel-based reformulation of the spatial $L^2$ bound for the bandlimited
tube projection. -/
theorem plancherel_bandlimited_tube_bound
    (φ : ℝ2 → ℂ) (hsmooth : ContDiff ℝ ⊤ φ)
    (hint : Integrable φ volume)
    (T : Tube) (hsupp : Function.support φ ⊆ T.toSet)
    (R : ℝ) (hR : 1 ≤ R) (hTR : T.R = R)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R)
    (hInt : Integrable (fun x => ‖cumulativeFreqProj φ r x‖ ^ 2) volume) :
    ∫ x, ‖cumulativeFreqProj φ r x‖ ^ 2 ≤ r⁻¹ * R := by

  simp only [cumulativeFreqProj] at hInt ⊢

  have hplanch := plancherel_fourierInv
    (fun ξ => (FourierTransform.fourier φ) ξ * (if dist ξ 0 ≤ 1 / r then (1 : ℂ) else 0))
    hInt
  rw [hplanch]

  exact tube_fourier_restricted_l2_bound φ hsmooth hint T hsupp R hR hTR r hr_pos hr_le

/-- Per-tube $L^2$ estimate: $\|P_{\leq 1/r}\varphi_T\|_{L^2}^2 \leq R/r$ for any
smooth integrable bump $\varphi_T$ supported in the tube $T$. -/
theorem freqLocalized_tube_l2_bound
    (T : Tube) (R : ℝ) (hR : 1 ≤ R) (hTR : T.R = R)
    (φ_T : ℝ2 → ℂ) (hsmooth : ContDiff ℝ ⊤ φ_T)
    (hint : Integrable φ_T volume) (hsupp : Function.support φ_T ⊆ T.toSet)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R) :
    l2NormSq (cumulativeFreqProj φ_T r) ≤ r⁻¹ * R := by
  unfold l2NormSq
  by_cases hInt : Integrable (fun x => ‖cumulativeFreqProj φ_T r x‖ ^ 2) volume
  · exact plancherel_bandlimited_tube_bound φ_T hsmooth hint T hsupp R hR hTR r hr_pos hr_le hInt
  · rw [integral_undef hInt]
    positivity

/-- The $L^2$ norm of the $k$-th Littlewood–Paley piece is dominated by the cumulative
frequency projection up to scale $2^k$. -/
theorem l2NormSq_littlewoodPaleyPieceK_le_cumulativeFreqProj
    (f : ℝ2 → ℂ) (hf_int : Integrable f volume)
    (K k : ℕ) (hk_le : k ≤ K) :
    l2NormSq (fun x => littlewoodPaleyPieceK f K k x) ≤
      l2NormSq (cumulativeFreqProj f ((2 : ℝ) ^ k)) := by sorry

/-- The cumulative frequency projection commutes with finite sums:
$\sum_i P_{\leq 1/r}\varphi_i = P_{\leq 1/r}(\sum_i \varphi_i)$. -/
theorem cumulativeFreqProj_sum
    {ι : Type*} (s : Finset ι) (φ : ι → ℝ2 → ℂ)
    (hint : ∀ i ∈ s, Integrable (φ i) volume)
    (r : ℝ) :
    (fun x => ∑ i ∈ s, cumulativeFreqProj (φ i) r x) =
      cumulativeFreqProj (fun x => ∑ i ∈ s, φ i x) r := by sorry

/-- $L^2$ norm of a Littlewood–Paley piece at scale $r$ is dominated by the $L^2$
norm of the sum of tube-wise cumulative frequency projections. -/
theorem lp_piece_bounded_by_proj_sum
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (r : ℝ) (hr : r ∈ dyadicRange R) :
    l2NormSq (littlewoodPaleyPiece 𝒯 φ R r) ≤
      l2NormSq (fun x => ∑ T ∈ 𝒯, cumulativeFreqProj (φ T) r x) := by

  show l2NormSq (fun x => littlewoodPaleyPieceK (fun x => ∑ T ∈ 𝒯, φ T x)
    (Nat.log 2 ⌊R⌋₊) (Nat.log 2 ⌊r⌋₊) x) ≤ _
  set f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  set K := Nat.log 2 ⌊R⌋₊
  set k := Nat.log 2 ⌊r⌋₊

  simp only [dyadicRange, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨⟨j, hj_lt, hj_eq⟩, _⟩ := hr

  have hk_eq : k = j := by
    show Nat.log 2 ⌊r⌋₊ = j
    rw [← hj_eq, nat_log_two_pow]

  have hk_le : k ≤ K := by omega

  have hf_int : Integrable f volume :=
    integrable_finset_sum 𝒯 (fun T hT => hφ_integrable T hT)

  have h1 := l2NormSq_littlewoodPaleyPieceK_le_cumulativeFreqProj f hf_int K k hk_le

  have h_rhs : (fun x => ∑ T ∈ 𝒯, cumulativeFreqProj (φ T) r x) =
      cumulativeFreqProj f r :=
    cumulativeFreqProj_sum 𝒯 φ hφ_integrable r
  rw [h_rhs]

  have h_scale : (2 : ℝ) ^ k = r := by rw [hk_eq, hj_eq]
  rw [← h_scale]
  exact h1

/-- The pairwise interaction $\langle g, F\rangle_{\mathbb R} = \mathrm{Re} \int
\overline{g(x)} F(x)\, dx$ between two complex-valued functions. -/
def tubeInteraction (g F : ℝ2 → ℂ) : ℝ :=
  ∫ x, ((starRingEnd ℂ) (g x) * F x).re

/-- Pointwise expansion of $\|\sum_T g(T)\|^2$ as $\sum_T \mathrm{Re}(\overline{g(T)}
\sum_{T'} g(T'))$. -/
lemma norm_sq_sum_eq_sum_re_tube (𝒯 : Finset Tube) (g : Tube → ℂ) :
    ‖∑ T ∈ 𝒯, g T‖ ^ 2 = ∑ T ∈ 𝒯, ((starRingEnd ℂ) (g T) * ∑ T' ∈ 𝒯, g T').re := by
  have h1 := Complex.sq_norm (∑ T ∈ 𝒯, g T)
  rw [h1]
  have h2 : ∀ z : ℂ, Complex.normSq z = ((starRingEnd ℂ) z * z).re := by
    intro z; simp [Complex.normSq]
  rw [h2, map_sum (starRingEnd ℂ), Finset.sum_mul]
  simp only [Complex.re_sum]

/-- $L^2$ norm of a tube sum equals the sum of tube interactions:
$\|\sum_T g_T\|_{L^2}^2 = \sum_T \langle g_T, \sum_{T'} g_{T'}\rangle$. -/
lemma l2NormSq_sum_eq_sum_interaction (𝒯 : Finset Tube) (g : Tube → ℝ2 → ℂ)
    (hint : ∀ T ∈ 𝒯, Integrable (fun x => ((starRingEnd ℂ) (g T x) *
      ∑ T' ∈ 𝒯, g T' x).re) volume) :
    l2NormSq (fun x => ∑ T ∈ 𝒯, g T x) =
    ∑ T ∈ 𝒯, tubeInteraction (g T) (fun x => ∑ T' ∈ 𝒯, g T' x) := by
  unfold l2NormSq tubeInteraction
  simp_rw [norm_sq_sum_eq_sum_re_tube 𝒯 (fun T => g T _)]
  exact integral_finset_sum 𝒯 hint

/-- The pairwise interaction $\langle P_{\leq 1/r}\varphi_T, P_{\leq 1/r}\varphi_{T'}\rangle$
between two tube projections is integrable. -/
theorem pairwise_freq_interaction_integrable
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (T T' : Tube) (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯) :
    Integrable (fun x => ((starRingEnd ℂ) (cumulativeFreqProj (φ T) r x) *
      cumulativeFreqProj (φ T') r x).re) volume := by sorry

/-- Per-tube $L^2$ bound restated as a wrapper for tubes belonging to a collection:
$\|P_{\leq 1/r}\varphi_T\|_{L^2}^2 \leq R/r$. -/
theorem cumulativeFreqProj_l2NormSq_comparable
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R)
    (T : Tube) (hT : T ∈ 𝒯) :
    l2NormSq (cumulativeFreqProj (φ T) r) ≤ r⁻¹ * R := by
  have hr_pos : (0 : ℝ) < r := pos_of_mem_dyadicRange hr
  have hr_le : r ≤ R := by
    simp only [dyadicRange, Finset.mem_filter] at hr; exact hr.2
  exact freqLocalized_tube_l2_bound T R hR (hR_eq T hT) (φ T) (hφ_smooth T hT)
    (hφ_integrable T hT) (hφ_support T hT) r hr_pos hr_le

/-- Cauchy–Schwarz bound on pairwise tube interactions (for neighbors): when both
tubes lie in a common $r \times R$ wide tube,
$|\langle P_{\leq 1/r}\varphi_T, P_{\leq 1/r}\varphi_{T'}\rangle| \leq R/r$. -/
theorem pairwise_interaction_cauchy_schwarz
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R)
    (T T' : Tube) (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯)
    (hcontained : ∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
      T.containedIn W ∧ T'.containedIn W) :
    tubeInteraction (cumulativeFreqProj (φ T) r) (cumulativeFreqProj (φ T') r) ≤
      r⁻¹ * R := by

  set g := cumulativeFreqProj (φ T) r
  set F := cumulativeFreqProj (φ T') r

  have hA_bound : l2NormSq g ≤ r⁻¹ * R :=
    cumulativeFreqProj_l2NormSq_comparable 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable
      hφ_support r hr T hT
  have hB_bound : l2NormSq F ≤ r⁻¹ * R :=
    cumulativeFreqProj_l2NormSq_comparable 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable
      hφ_support r hr T' hT'

  unfold tubeInteraction l2NormSq at *
  by_cases hi : Integrable (fun x => ((starRingEnd ℂ) (g x) * F x).re) volume
  ·

    have hr_pos : (0 : ℝ) < r := by
      simp only [dyadicRange, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hr
      obtain ⟨⟨k, _, hk⟩, _⟩ := hr; rw [← hk]; positivity
    have hr_le : r ≤ R := by
      simp only [dyadicRange, Finset.mem_filter] at hr; exact hr.2

    have hig : Integrable (fun x => ‖g x‖ ^ 2) volume :=
      tube_freq_loc_spatial_integrable (φ T) (hφ_smooth T hT) (hφ_integrable T hT)
        T (hφ_support T hT) R hR (hR_eq T hT) r hr_pos hr_le
    have hiF : Integrable (fun x => ‖F x‖ ^ 2) volume :=
      tube_freq_loc_spatial_integrable (φ T') (hφ_smooth T' hT') (hφ_integrable T' hT')
        T' (hφ_support T' hT') R hR (hR_eq T' hT') r hr_pos hr_le

    have hpw : ∀ x : ℝ2,
        ((starRingEnd ℂ) (g x) * F x).re ≤ (‖g x‖ ^ 2 + ‖F x‖ ^ 2) / 2 := by
      intro x
      have h1 : ((starRingEnd ℂ) (g x) * F x).re ≤ ‖g x‖ * ‖F x‖ := by
        calc ((starRingEnd ℂ) (g x) * F x).re
            ≤ ‖(starRingEnd ℂ) (g x) * F x‖ := Complex.re_le_norm _
          _ = ‖g x‖ * ‖F x‖ := by rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖g x‖ - ‖F x‖)]

    have hint_sum : Integrable (fun x => (‖g x‖ ^ 2 + ‖F x‖ ^ 2) / 2) volume :=
      (hig.add hiF).div_const 2

    set A := ∫ x, ‖g x‖ ^ 2
    set B := ∫ x, ‖F x‖ ^ 2
    have h_avg : ∫ x, (‖g x‖ ^ 2 + ‖F x‖ ^ 2) / 2 = (A + B) / 2 := by
      rw [integral_div, integral_add hig hiF]
    calc ∫ x, ((starRingEnd ℂ) (g x) * F x).re
        ≤ ∫ x, (‖g x‖ ^ 2 + ‖F x‖ ^ 2) / 2 := integral_mono hi hint_sum hpw
      _ = (A + B) / 2 := h_avg
      _ ≤ (r⁻¹ * R + r⁻¹ * R) / 2 := by linarith
      _ = r⁻¹ * R := by ring
  ·
    rw [integral_undef hi]
    have hr_pos : (0 : ℝ) < r := pos_of_mem_dyadicRange hr
    positivity

/-- For tubes $T, T'$ that do not share any common $r \times R$ containing rectangle,
the tube interaction vanishes. -/
theorem non_neighbor_interaction_vanishes
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R)
    (T T' : Tube) (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯)
    (hnot_contained : ¬∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
      T.containedIn W ∧ T'.containedIn W) :
    tubeInteraction (cumulativeFreqProj (φ T) r) (cumulativeFreqProj (φ T') r) = 0 := by sorry

/-- Non-positivity (in fact zero) of interactions for non-neighboring tube pairs. -/
theorem negligible_interaction_non_neighbors
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R)
    (T T' : Tube) (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯)
    (hnot_contained : ¬∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
      T.containedIn W ∧ T'.containedIn W) :
    tubeInteraction (cumulativeFreqProj (φ T) r) (cumulativeFreqProj (φ T') r) ≤ 0 := by
  rw [non_neighbor_interaction_vanishes 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable
    hφ_support r hr T T' hT hT' hnot_contained]

open Classical in
/-- Transitivity-of-containment for wide tubes of the same dimensions:
if $T$ lies in both $W_0$ and $W$, and $T'$ also lies in $W$, then $T'$ lies in $W_0$. -/
theorem wideTube_containment_through_shared_tube
    (T T' : Tube) (W W₀ : WideTube)
    (hWw : W.halfWidth = W₀.halfWidth) (hWl : W.halfLength = W₀.halfLength)
    (hTW₀ : T.containedIn W₀) (hTW : T.containedIn W)
    (hT'W : T'.containedIn W) :
    T'.containedIn W₀ := by sorry

open Classical in
/-- The number of tubes that share an $r \times R$ wide tube with `T` is at most
the tube covering number $N_\mathcal{T}(r)$. -/
theorem neighbor_counting_bound
    (𝒯 : Finset Tube) (R r : ℝ) (hR : 1 ≤ R)
    (T : Tube) (hT : T ∈ 𝒯) :
    (𝒯.filter (fun T' => ∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
      Tube.containedIn T W ∧ Tube.containedIn T' W)).card ≤ tubeCoveringNumber 𝒯 R r := by
  classical
  set neighborFilter := 𝒯.filter (fun T' => ∃ W : WideTube, W.halfWidth = r ∧ W.halfLength = R ∧
      Tube.containedIn T W ∧ Tube.containedIn T' W)
  by_cases h : neighborFilter = ∅
  · simp [h]
  · obtain ⟨T₀, hT₀mem⟩ := Finset.nonempty_of_ne_empty h
    obtain ⟨_, W₀, hW₀w, hW₀l, hTW₀, _⟩ := Finset.mem_filter.mp hT₀mem
    have h_sub : neighborFilter ⊆ 𝒯.filter (fun T' => T'.containedIn W₀) := by
      intro T' hT'
      rw [Finset.mem_filter] at hT' ⊢
      refine ⟨hT'.1, ?_⟩
      obtain ⟨_, W, hWw, hWl, hTW, hT'W⟩ := hT'
      exact wideTube_containment_through_shared_tube T T' W W₀
        (by rw [hWw, hW₀w]) (by rw [hWl, hW₀l]) hTW₀ hTW hT'W
    calc neighborFilter.card
        ≤ (𝒯.filter (fun T' => T'.containedIn W₀)).card := Finset.card_le_card h_sub
      _ ≤ tubeCoveringNumber 𝒯 R r := by
          apply le_csSup_of_le
          · exact ⟨𝒯.card, fun n hn => by
              obtain ⟨W, _, _, heq⟩ := hn; rw [heq]; exact Finset.card_filter_le _ _⟩
          · exact ⟨W₀, hW₀w, hW₀l, rfl⟩
          · exact le_refl _

/-- Row-sum bound: for each tube $T$,
$\sum_{T' \in \mathcal{T}} \langle P_{\leq 1/r}\varphi_T, P_{\leq 1/r}\varphi_{T'}\rangle
\leq N_\mathcal{T}(r) \cdot (R/r)$. Combines orthogonality on non-neighbors with the
Cauchy–Schwarz bound on neighbors. -/
theorem orthogonality_interaction_sum_bound
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R)
    (T : Tube) (hT : T ∈ 𝒯) :
    ∑ T' ∈ 𝒯, tubeInteraction (cumulativeFreqProj (φ T) r) (cumulativeFreqProj (φ T') r) ≤
      (tubeCoveringNumber 𝒯 R r : ℝ) * (r⁻¹ * R) := by
  classical

  set isNeighbor : Tube → Prop := fun T' => ∃ W : WideTube, W.halfWidth = r ∧
    W.halfLength = R ∧ T.containedIn W ∧ T'.containedIn W

  have hsplit : ∑ T' ∈ 𝒯, tubeInteraction (cumulativeFreqProj (φ T) r)
      (cumulativeFreqProj (φ T') r) =
    ∑ T' ∈ 𝒯.filter isNeighbor, tubeInteraction (cumulativeFreqProj (φ T) r)
      (cumulativeFreqProj (φ T') r) +
    ∑ T' ∈ 𝒯.filter (fun T' => ¬isNeighbor T'), tubeInteraction (cumulativeFreqProj (φ T) r)
      (cumulativeFreqProj (φ T') r) := by
    rw [← Finset.sum_filter_add_sum_filter_not 𝒯 isNeighbor]
  rw [hsplit]

  have hnn : ∑ T' ∈ 𝒯.filter (fun T' => ¬isNeighbor T'),
      tubeInteraction (cumulativeFreqProj (φ T) r) (cumulativeFreqProj (φ T') r) ≤ 0 := by
    apply Finset.sum_nonpos
    intro T' hT'
    rw [Finset.mem_filter] at hT'
    exact negligible_interaction_non_neighbors 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable
      hφ_support r hr T T' hT hT'.1 hT'.2

  have hneighbor : ∑ T' ∈ 𝒯.filter isNeighbor,
      tubeInteraction (cumulativeFreqProj (φ T) r) (cumulativeFreqProj (φ T') r) ≤
      (tubeCoveringNumber 𝒯 R r : ℝ) * (r⁻¹ * R) := by
    calc ∑ T' ∈ 𝒯.filter isNeighbor,
          tubeInteraction (cumulativeFreqProj (φ T) r) (cumulativeFreqProj (φ T') r)
        ≤ ∑ T' ∈ 𝒯.filter isNeighbor, (r⁻¹ * R) := by
          apply Finset.sum_le_sum
          intro T' hT'
          rw [Finset.mem_filter] at hT'
          exact pairwise_interaction_cauchy_schwarz 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable
            hφ_support r hr T T' hT hT'.1 hT'.2
      _ = (𝒯.filter isNeighbor).card • (r⁻¹ * R) := by
          rw [Finset.sum_const]
      _ = ((𝒯.filter isNeighbor).card : ℝ) * (r⁻¹ * R) := by
          rw [nsmul_eq_mul]
      _ ≤ (tubeCoveringNumber 𝒯 R r : ℝ) * (r⁻¹ * R) := by
          apply mul_le_mul_of_nonneg_right
          · have hcount := @neighbor_counting_bound 𝒯 R r hR T hT
            exact_mod_cast hcount
          · have hr_pos : (0 : ℝ) < r := pos_of_mem_dyadicRange hr
            positivity

  linarith

/-- Per-tube interaction bound: $\langle P_{\leq 1/r}\varphi_T, \sum_{T'}
P_{\leq 1/r}\varphi_{T'}\rangle \leq N_\mathcal{T}(r) \cdot (R/r)$, obtained by
expanding the right-hand side via linearity of integration. -/
theorem per_tube_interaction_bound
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R)
    (T : Tube) (hT : T ∈ 𝒯) :
    tubeInteraction (cumulativeFreqProj (φ T) r)
      (fun x => ∑ T' ∈ 𝒯, cumulativeFreqProj (φ T') r x) ≤
      (tubeCoveringNumber 𝒯 R r : ℝ) * (r⁻¹ * R) := by


  have hlin : tubeInteraction (cumulativeFreqProj (φ T) r)
      (fun x => ∑ T' ∈ 𝒯, cumulativeFreqProj (φ T') r x) =
      ∑ T' ∈ 𝒯, tubeInteraction (cumulativeFreqProj (φ T) r)
        (cumulativeFreqProj (φ T') r) := by
    unfold tubeInteraction
    simp_rw [Finset.mul_sum, Complex.re_sum]
    exact integral_finset_sum 𝒯 (fun T' hT' =>
      pairwise_freq_interaction_integrable 𝒯 R hR φ hφ_smooth hφ_integrable
        hφ_support r T T' hT hT')

  rw [hlin]
  exact orthogonality_interaction_sum_bound 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable
    hφ_support r hr T hT

/-- Integrability of the interaction between a single tube projection and the sum
of all tube projections. -/
theorem interaction_integrable
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (T : Tube) (hT : T ∈ 𝒯) :
    Integrable (fun x => ((starRingEnd ℂ) (cumulativeFreqProj (φ T) r x) *
      ∑ T' ∈ 𝒯, cumulativeFreqProj (φ T') r x).re) volume := by sorry

/-- $L^2$ orthogonality counting bound: $\|\sum_T P_{\leq 1/r}\varphi_T\|_{L^2}^2 \leq
N_\mathcal{T}(r) \cdot |\mathcal{T}| \cdot (R/r)$. -/
theorem orthogonality_counting_for_tubes
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R) :
    l2NormSq (fun x => ∑ T ∈ 𝒯, cumulativeFreqProj (φ T) r x) ≤
      (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * (r⁻¹ * R) := by

  have hint : ∀ T ∈ 𝒯, Integrable (fun x => ((starRingEnd ℂ)
      (cumulativeFreqProj (φ T) r x) * ∑ T' ∈ 𝒯, cumulativeFreqProj (φ T') r x).re) volume :=
    fun T hT => interaction_integrable 𝒯 R hR φ hφ_smooth hφ_integrable hφ_support r T hT
  rw [l2NormSq_sum_eq_sum_interaction 𝒯 (fun T => cumulativeFreqProj (φ T) r) hint]

  calc ∑ T ∈ 𝒯, tubeInteraction (cumulativeFreqProj (φ T) r)
        (fun x => ∑ T' ∈ 𝒯, cumulativeFreqProj (φ T') r x)
      ≤ ∑ T ∈ 𝒯, ((tubeCoveringNumber 𝒯 R r : ℝ) * (r⁻¹ * R)) := by
        apply Finset.sum_le_sum
        intro T hT
        exact per_tube_interaction_bound 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable
          hφ_support r hr T hT

    _ = (𝒯.card : ℝ) * ((tubeCoveringNumber 𝒯 R r : ℝ) * (r⁻¹ * R)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * (r⁻¹ * R) := by ring

/-- Direct $L^2$ bound on the Littlewood–Paley piece $f_r$ via orthogonality counting:
$\|f_r\|_{L^2}^2 \leq N_\mathcal{T}(r) \cdot |\mathcal{T}| \cdot (R/r)$. -/
theorem l2_orthogonality_counting
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet)
    (r : ℝ) (hr : r ∈ dyadicRange R)
    (hint : Integrable (fun x => ‖littlewoodPaleyPiece 𝒯 φ R r x‖ ^ 2) volume) :
    l2NormSq (littlewoodPaleyPiece 𝒯 φ R r) ≤
      (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * (r⁻¹ * R) := by
  calc l2NormSq (littlewoodPaleyPiece 𝒯 φ R r)
      ≤ l2NormSq (fun x => ∑ T ∈ 𝒯, cumulativeFreqProj (φ T) r x) :=
        lp_piece_bounded_by_proj_sum 𝒯 R hR φ hφ_smooth hφ_integrable r hr
    _ ≤ (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * (r⁻¹ * R) :=
        orthogonality_counting_for_tubes 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable hφ_support r hr

/-- Final per-scale $L^2$ estimate for the Littlewood–Paley pieces:
$\|f_r\|_{L^2}^2 \leq N_\mathcal{T}(r) \cdot |\mathcal{T}| \cdot R / r$. -/
theorem littlewoodPaley_l2_estimate
    (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet) :
    ∀ r ∈ dyadicRange R,
      l2NormSq (littlewoodPaleyPiece 𝒯 φ R r) ≤
        1 * (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * r⁻¹ * R := by
  intro r hr
  by_cases hint : Integrable (fun x => ‖littlewoodPaleyPiece 𝒯 φ R r x‖ ^ 2) volume
  ·
    have h1 := l2_orthogonality_counting 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable hφ_support r hr hint
    linarith
  ·
    unfold l2NormSq
    rw [integral_undef hint]
    have hr_pos : (0 : ℝ) < r := pos_of_mem_dyadicRange hr
    positivity

/-- **Main Lemma (real version).** Let $\mathcal{T}$ be a finite set of $1 \times R$
tubes in $\mathbb{R}^2$ and $\varphi_T$ a smooth integrable bump supported on each
tube. Then there exists a Littlewood–Paley frequency decomposition
$f = \sum_T \varphi_T = \sum_{r \in \text{dyadic}} f_r$ with $\hat{f_r}$ supported in
$\{|\xi| \leq 1/r\}$ and the per-scale $L^2$ estimate
$\|f_r\|_{L^2}^2 \leq N_\mathcal{T}(r) \cdot |\mathcal{T}| \cdot R / r$. -/
theorem main_lemma_real (𝒯 : Finset Tube) (R : ℝ) (hR : 1 ≤ R)
    (hR_eq : ∀ T ∈ 𝒯, T.R = R)
    (φ : Tube → ℝ2 → ℂ) (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
    (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
    (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet) :
    ∃ data : FrequencyDecompositionData 𝒯 R, data.φ = φ :=
  ⟨{ φ := φ
     f_r := littlewoodPaleyPiece 𝒯 φ R
     decomposition :=
       littlewoodPaley_decomposition 𝒯 R hR φ hφ_smooth hφ_integrable hφ_support
     freq_support :=
       littlewoodPaley_freq_support 𝒯 R hR φ hφ_smooth hφ_integrable hφ_support
     C := 1
     hC := one_pos
     l2_estimate :=
       littlewoodPaley_l2_estimate 𝒯 R hR hR_eq φ hφ_smooth hφ_integrable hφ_support
   }, rfl⟩

end FrequencyDecomposition
