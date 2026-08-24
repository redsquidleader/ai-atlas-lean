/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace OrthogonalityTubes

open MeasureTheory

/-- The perpendicular vector in $\mathbb{R}^2$: $\mathrm{perp}(d_0, d_1) = (-d_1, d_0)$. -/
def perp (d : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(d 1), d 0]

/-- Underlying point set of a rectangle with centre $c$, axis-direction $d$, width $w$ and
length $l$: the set of $x$ with $|\langle x - c, d\rangle| \le l/2$ and
$|\langle x - c, d^\perp\rangle| \le w/2$. -/
def rectangleCarrier (c d : EuclideanSpace ℝ (Fin 2)) (w l : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |@inner ℝ _ _ (x - c) d| ≤ l / 2 ∧ |@inner ℝ _ _ (x - c) (perp d)| ≤ w / 2}

/-- A *tube* of length $R$ in $\mathbb{R}^2$: an oriented $1 \times R$ rectangle parameterised
by a centre point and a unit direction vector. -/
structure Tube (R : ℝ) where
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

/-- The underlying point set of a tube $T$: the $1 \times R$ rectangle with axis along
`T.direction` centred at `T.center`. -/
def Tube.carrier {R : ℝ} (T : Tube R) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleCarrier T.center T.direction 1 R

/-- The open $r$-thickening of a tube's carrier (the set of points within distance $r$). -/
def Tube.rNeighborhood {R : ℝ} (T : Tube R) (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.thickening r T.carrier

/-- An oriented rectangle in $\mathbb{R}^2$ of given width and length, parameterised by a
centre and a unit direction (the axis of the rectangle). -/
structure Rectangle (width length : ℝ) where
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

/-- The underlying point set of a `Rectangle`: a $w \times l$ rectangle centred at
`rect.center` with axis `rect.direction`. -/
def Rectangle.carrier {w l : ℝ} (rect : Rectangle w l) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleCarrier rect.center rect.direction w l

/-- A tube `T` is *contained in* a rectangle `rect` if its carrier is a subset of the
rectangle's carrier. -/
def Tube.containedIn {R : ℝ} (T : Tube R) {w l : ℝ} (rect : Rectangle w l) : Prop :=
  T.carrier ⊆ rect.carrier

/-- The standard bilinear pairing $(v, w) \mapsto \langle v, w\rangle$ on
$\mathbb{R}^2$, packaged as a continuous bilinear map (used to define the Fourier
transform on $\mathbb{R}^2$). -/
def stdBilinR2 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ where
  toFun v := {
    toFun := fun w => @inner ℝ _ _ v w
    map_add' := fun w₁ w₂ => by simp [inner_add_right]
    map_smul' := fun c w => by simp [inner_smul_right]
  }
  map_add' := fun v₁ v₂ => by ext w; simp [inner_add_left]
  map_smul' := fun c v => by ext w; simp [inner_smul_left]

/-- The Fourier transform on $\mathbb{R}^2$:
$\widehat f(\xi) = \int_{\mathbb{R}^2} f(x)\, e^{-2\pi i \langle x, \xi\rangle}\, dx$. -/
def fourierTransformR2 (f : EuclideanSpace ℝ (Fin 2) → ℂ) :
    EuclideanSpace ℝ (Fin 2) → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume stdBilinR2 f

/-- The frequency annulus at scale $r$: $\{\xi : r^{-1}/2 \le \|\xi\| \le 2 r^{-1}\}$. -/
def freqAnnulus (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {ξ | r⁻¹ / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * r⁻¹}

/-- The frequency-localised wave packet $\phi_{T, r}$ associated to a tube $T$ at scale $r$:
a function whose Fourier transform is concentrated in an angular cap of width $\sim r/R$
around the direction of $T$. -/
noncomputable def phiTubeFreqLoc (R r : ℝ) (T : Tube R) : (EuclideanSpace ℝ (Fin 2) → ℂ) := by sorry

/-- The frequency angular cap supporting $\widehat{\phi_{T, r}}$: frequencies in the annulus
of scale $r$ that lie within angular distance $\lesssim r / R$ of the line $\mathbb{R} \cdot
T.\mathrm{direction}$. -/
def freqAngularCap (R r : ℝ) (T : Tube R) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {ξ | ξ ∈ freqAnnulus r ∧ ‖ξ - (‖ξ‖ • T.direction)‖ ≤ (r / (3 * R)) * ‖ξ‖}

/-- Angular Fourier support of the tube wave packet: $\widehat{\phi_{T, r}}$ vanishes outside
the frequency angular cap of $T$. -/
theorem phiTubeFreqLoc_angularSupport (R r : ℝ) (hR : 1 ≤ R) (hr : 0 < r) (hrR : r ≤ R)
    (T : Tube R) :
    ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ξ ∉ freqAngularCap R r T → fourierTransformR2 (phiTubeFreqLoc R r T) ξ = 0 := by sorry

/-- The $L^2$ inner product $\langle f, g\rangle = \int f(x) \overline{g(x)}\, dx$ on
$\mathbb{R}^2$. -/
def l2Inner (f g : EuclideanSpace ℝ (Fin 2) → ℂ) : ℂ :=
  ∫ x, f x * starRingEnd ℂ (g x) ∂volume

/-- A surrogate for the angle between two tubes: $\|T_1.\text{direction} -
T_2.\text{direction}\|$ (which is comparable to $|\sin \theta|$ for the actual angle
$\theta$ between the directions when both are unit vectors). -/
def Tube.angle {R : ℝ} (T₁ T₂ : Tube R) : ℝ :=
  ‖T₁.direction - T₂.direction‖

/-- **Plancherel's theorem** on $\mathbb{R}^2$:
$\langle f, g\rangle_{L^2} = \langle \widehat f, \widehat g\rangle_{L^2}$. -/
theorem plancherel_l2Inner (f g : EuclideanSpace ℝ (Fin 2) → ℂ) :
    l2Inner f g = l2Inner (fourierTransformR2 f) (fourierTransformR2 g) := by sorry

/-- If two tubes have angular separation $\ge R^\varepsilon \cdot r/R$ then the Fourier
supports of their wave packets $\phi_{T_1, r}, \phi_{T_2, r}$ are disjoint: at every frequency
$\xi$, at least one of the Fourier transforms vanishes. -/
theorem phiTubeFreqLoc_disjoint_fourierSupport
    {R : ℝ} (hR : 1 ≤ R) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {ε : ℝ} (hε : 0 < ε)
    (T₁ T₂ : Tube R) (hangle : T₁.angle T₂ ≥ R ^ ε * (r / R)) :
    ∀ ξ : EuclideanSpace ℝ (Fin 2),
      fourierTransformR2 (phiTubeFreqLoc R r T₁) ξ = 0 ∨
      fourierTransformR2 (phiTubeFreqLoc R r T₂) ξ = 0 := by
  intro ξ
  by_cases h₁ : ξ ∈ freqAngularCap R r T₁
  ·
    right
    apply phiTubeFreqLoc_angularSupport R r hR hr hrR T₂ ξ
    intro h₂
    simp only [freqAngularCap, freqAnnulus, Set.mem_setOf_eq] at h₁ h₂
    obtain ⟨⟨hann_lo, _⟩, hcap₁⟩ := h₁
    obtain ⟨_, hcap₂⟩ := h₂
    have hξ_pos : (0 : ℝ) < ‖ξ‖ := by linarith [show r⁻¹ / 2 > 0 from by positivity]
    have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
    have hrR_pos : (0 : ℝ) < r / R := div_pos hr hR_pos

    have hangle_bound : ‖T₁.direction - T₂.direction‖ ≤ 2 * (r / (3 * R)) := by
      have heq : ‖(‖ξ‖ • T₁.direction) - (‖ξ‖ • T₂.direction)‖ =
          ‖ξ‖ * ‖T₁.direction - T₂.direction‖ := by
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (norm_nonneg ξ)]
      have hineq : ‖(‖ξ‖ • T₁.direction) - (‖ξ‖ • T₂.direction)‖ ≤
          2 * (r / (3 * R)) * ‖ξ‖ := by
        calc ‖(‖ξ‖ • T₁.direction) - (‖ξ‖ • T₂.direction)‖
            = ‖(‖ξ‖ • T₁.direction - ξ) + (ξ - ‖ξ‖ • T₂.direction)‖ := by congr 1; abel
          _ ≤ ‖‖ξ‖ • T₁.direction - ξ‖ + ‖ξ - ‖ξ‖ • T₂.direction‖ := norm_add_le _ _
          _ = ‖ξ - ‖ξ‖ • T₁.direction‖ + ‖ξ - ‖ξ‖ • T₂.direction‖ := by rw [norm_sub_rev]
          _ ≤ (r / (3 * R)) * ‖ξ‖ + (r / (3 * R)) * ‖ξ‖ := add_le_add hcap₁ hcap₂
          _ = 2 * (r / (3 * R)) * ‖ξ‖ := by ring
      nlinarith [heq ▸ hineq]

    unfold Tube.angle at hangle
    have h_combined : R ^ ε * (r / R) ≤ 2 / 3 * (r / R) := by
      have : 2 * (r / (3 * R)) = 2 / 3 * (r / R) := by ring
      linarith
    have hReps_le : R ^ ε ≤ 2 / 3 := le_of_mul_le_mul_of_pos_right h_combined hrR_pos
    have hReps_ge : R ^ ε ≥ 1 := Real.one_le_rpow hR (le_of_lt hε)
    linarith
  ·
    left
    exact phiTubeFreqLoc_angularSupport R r hR hr hrR T₁ ξ h₁

/-- If at every point $\xi$ either $f(\xi) = 0$ or $g(\xi) = 0$, then $\langle f, g\rangle =
0$ — the integrand vanishes identically. -/
lemma l2Inner_eq_zero_of_pointwise_disjoint
    (f g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (h : ∀ ξ, f ξ = 0 ∨ g ξ = 0) :
    l2Inner f g = 0 := by
  unfold l2Inner
  have heq : (fun x => f x * starRingEnd ℂ (g x)) = 0 := by
    ext x
    cases h x with
    | inl hf => simp [hf]
    | inr hg => simp [hg]
  rw [heq]
  simp

/-- Orthogonality of tube wave packets (angular case): if the tubes have angular separation
$\ge R^\varepsilon \cdot r/R$, then $\langle \phi_{T_1, r}, \phi_{T_2, r}\rangle = 0$ exactly.
Proof: Plancherel plus disjoint Fourier supports. -/
theorem orthogonality_tubes_case_angle
    {R : ℝ} (hR : 1 ≤ R)
    {r : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R)
    {ε : ℝ} (hε : 0 < ε)
    (T₁ T₂ : Tube R)
    (hangle : T₁.angle T₂ ≥ R ^ ε * (r / R)) :
    l2Inner (phiTubeFreqLoc R r T₁) (phiTubeFreqLoc R r T₂) = 0 := by
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr

  have hdisjoint := phiTubeFreqLoc_disjoint_fourierSupport hR hr_pos hrR hε T₁ T₂ hangle

  rw [plancherel_l2Inner]

  exact l2Inner_eq_zero_of_pointwise_disjoint _ _ hdisjoint

/-- For $R \ge 1$, the carrier of every tube is nonempty (the centre belongs to it). -/
lemma Tube.carrier_nonempty {R : ℝ} (hR : 1 ≤ R) (T : Tube R) :
    (T.carrier : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
  refine ⟨T.center, ?_⟩
  simp only [Tube.carrier, rectangleCarrier, Set.mem_setOf_eq, sub_self, inner_zero_left,
    abs_zero]
  exact ⟨by linarith, by linarith⟩

/-- If the $r$-thickenings of two tubes are disjoint, then for every point $x$ at least one of
the two tubes lies at distance $\ge r$ from $x$. -/
lemma disjoint_thickening_infDist {R : ℝ} (hR : 1 ≤ R)
    {r : ℝ} (T₁ T₂ : Tube R)
    (hdisjoint : Disjoint (T₁.rNeighborhood r) (T₂.rNeighborhood r))
    (x : EuclideanSpace ℝ (Fin 2)) :
    r ≤ Metric.infDist x T₁.carrier ∨ r ≤ Metric.infDist x T₂.carrier := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hx1 : x ∈ T₁.rNeighborhood r := by
    simp only [Tube.rNeighborhood]
    rwa [Metric.mem_thickening_iff_infDist_lt (Tube.carrier_nonempty hR T₁)]
  have hx2 : x ∈ T₂.rNeighborhood r := by
    simp only [Tube.rNeighborhood]
    rwa [Metric.mem_thickening_iff_infDist_lt (Tube.carrier_nonempty hR T₂)]
  exact hdisjoint.ne_of_mem hx1 hx2 rfl

/-- Schwartz-type pointwise decay bound for the tube wave packet:
$|\phi_{T, r}(x)| \le r^{-1} (1 + d(x, T) / r)^{-N}$ for every $N > 0$. -/
theorem phiTubeFreqLoc_schwartz_bound (R r : ℝ) (hR : 1 ≤ R) (hr : 1 ≤ r)
    (hrR : r ≤ R) (T : Tube R) (N : ℝ) (hN : 0 < N) :
    ∀ x : EuclideanSpace ℝ (Fin 2),
      ‖phiTubeFreqLoc R r T x‖ ≤ r⁻¹ * (1 + Metric.infDist x T.carrier / r) ^ (-N) := by sorry

/-- The tube wave packet $\phi_{T, r}$ is absolutely integrable on $\mathbb{R}^2$ — its norm
function lies in $L^1$. -/
theorem phiTubeFreqLoc_norm_integrable (R r : ℝ) (hR : 1 ≤ R) (hr : 1 ≤ r)
    (hrR : r ≤ R) (T : Tube R) :
    Integrable (fun x => ‖phiTubeFreqLoc R r T x‖) volume := by sorry

/-- $L^1$ bound on the tube wave packet:
$\int_{\mathbb{R}^2} |\phi_{T, r}(x)|\, dx \le R/4$. -/
theorem phiTubeFreqLoc_l1_le (R r : ℝ) (hR : 1 ≤ R) (hr : 1 ≤ r)
    (hrR : r ≤ R) (T : Tube R) :
    ∫ x, ‖phiTubeFreqLoc R r T x‖ ∂volume ≤ R / 4 := by sorry

/-- If two tubes are $r$-separated, then the pointwise product of their wave packets satisfies
$\int_{\mathbb{R}^2} |\phi_{T_1, r}(x) \overline{\phi_{T_2, r}(x)}|\, dx \le R^{-1000}$
(rapid decay from Schwartz estimates plus the $r$-separation). -/
theorem phiTubeFreqLoc_product_integral_bound
    {R : ℝ} (hR : 1 ≤ R)
    {r : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R)
    (T₁ T₂ : Tube R)
    (hdisjoint : Disjoint (T₁.rNeighborhood r) (T₂.rNeighborhood r)) :
    ∫ x, ‖phiTubeFreqLoc R r T₁ x * starRingEnd ℂ (phiTubeFreqLoc R r T₂ x)‖ ∂volume ≤
      R ^ (-(1000 : ℝ)) := by

  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 2),
      ‖phiTubeFreqLoc R r T₁ x * starRingEnd ℂ (phiTubeFreqLoc R r T₂ x)‖ =
      ‖phiTubeFreqLoc R r T₁ x‖ * ‖phiTubeFreqLoc R r T₂ x‖ := fun x => by
    rw [norm_mul, RCLike.norm_conj]
  simp_rw [hnorm]

  have hfar := disjoint_thickening_infDist hR T₁ T₂ hdisjoint
  have hr_pos : (0:ℝ) < r := by linarith
  have hR_pos : (0:ℝ) < R := by linarith

  set N := 1001 * Real.logb 2 R + 3
  have hN_pos : 0 < N := by
    have : 0 ≤ Real.logb 2 R := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hR
    linarith

  have h2N : (2:ℝ) ^ (-N) ≤ R ^ (-(1001:ℝ)) := by
    show (2:ℝ) ^ (-(1001 * Real.logb 2 R + 3)) ≤ R ^ (-(1001:ℝ))
    rw [show -(1001 * Real.logb 2 R + 3) = Real.logb 2 R * (-1001) + (-3) from by ring]
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have hlogb : (2:ℝ) ^ (Real.logb 2 R * (-1001)) = R ^ (-(1001:ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) hR_pos]
    rw [hlogb]
    have h23 : (2:ℝ) ^ (-(3:ℝ)) ≤ 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      apply inv_le_one_of_one_le₀; norm_cast
    nlinarith [Real.rpow_nonneg (le_of_lt hR_pos) (-(1001:ℝ))]

  have hpw : ∀ x : EuclideanSpace ℝ (Fin 2),
      ‖phiTubeFreqLoc R r T₁ x‖ * ‖phiTubeFreqLoc R r T₂ x‖ ≤
      r⁻¹ * R ^ (-(1001:ℝ)) * (‖phiTubeFreqLoc R r T₁ x‖ + ‖phiTubeFreqLoc R r T₂ x‖) := by
    intro x
    cases hfar x with
    | inl h1 =>
      have hbd := phiTubeFreqLoc_schwartz_bound R r hR hr hrR T₁ N hN_pos x
      have hdiv : 1 ≤ Metric.infDist x T₁.carrier / r := (le_div_iff₀ hr_pos).mpr (by linarith)
      have hdecay : (1 + Metric.infDist x T₁.carrier / r) ^ (-N) ≤ (2:ℝ) ^ (-N) :=
        Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < 2) (by linarith) (by linarith)
      have hφ1 : ‖phiTubeFreqLoc R r T₁ x‖ ≤ r⁻¹ * R ^ (-(1001:ℝ)) :=
        le_trans hbd (by apply mul_le_mul_of_nonneg_left (le_trans hdecay h2N) (by positivity))
      calc ‖phiTubeFreqLoc R r T₁ x‖ * ‖phiTubeFreqLoc R r T₂ x‖
          ≤ (r⁻¹ * R ^ (-(1001:ℝ))) * ‖phiTubeFreqLoc R r T₂ x‖ :=
            mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)
        _ ≤ r⁻¹ * R ^ (-(1001:ℝ)) * (‖phiTubeFreqLoc R r T₁ x‖ + ‖phiTubeFreqLoc R r T₂ x‖) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (by positivity)
    | inr h2 =>
      have hbd := phiTubeFreqLoc_schwartz_bound R r hR hr hrR T₂ N hN_pos x
      have hdiv : 1 ≤ Metric.infDist x T₂.carrier / r := (le_div_iff₀ hr_pos).mpr (by linarith)
      have hdecay : (1 + Metric.infDist x T₂.carrier / r) ^ (-N) ≤ (2:ℝ) ^ (-N) :=
        Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < 2) (by linarith) (by linarith)
      have hφ2 : ‖phiTubeFreqLoc R r T₂ x‖ ≤ r⁻¹ * R ^ (-(1001:ℝ)) :=
        le_trans hbd (by apply mul_le_mul_of_nonneg_left (le_trans hdecay h2N) (by positivity))
      calc ‖phiTubeFreqLoc R r T₁ x‖ * ‖phiTubeFreqLoc R r T₂ x‖
          ≤ ‖phiTubeFreqLoc R r T₁ x‖ * (r⁻¹ * R ^ (-(1001:ℝ))) :=
            mul_le_mul_of_nonneg_left hφ2 (norm_nonneg _)
        _ = r⁻¹ * R ^ (-(1001:ℝ)) * ‖phiTubeFreqLoc R r T₁ x‖ := by ring
        _ ≤ r⁻¹ * R ^ (-(1001:ℝ)) * (‖phiTubeFreqLoc R r T₁ x‖ + ‖phiTubeFreqLoc R r T₂ x‖) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (by positivity)

  have hint_bound : Integrable (fun x => r⁻¹ * R ^ (-(1001:ℝ)) *
      (‖phiTubeFreqLoc R r T₁ x‖ + ‖phiTubeFreqLoc R r T₂ x‖)) volume :=
    (Integrable.const_mul ((phiTubeFreqLoc_norm_integrable R r hR hr hrR T₁).add
      (phiTubeFreqLoc_norm_integrable R r hR hr hrR T₂)) _)
  have hle := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => by positivity))
    hint_bound
    (Filter.Eventually.of_forall hpw)

  have heval : ∫ x, r⁻¹ * R ^ (-(1001:ℝ)) *
      (‖phiTubeFreqLoc R r T₁ x‖ + ‖phiTubeFreqLoc R r T₂ x‖) ∂volume =
      r⁻¹ * R ^ (-(1001:ℝ)) * (∫ x, ‖phiTubeFreqLoc R r T₁ x‖ ∂volume +
        ∫ x, ‖phiTubeFreqLoc R r T₂ x‖ ∂volume) := by
    rw [← MeasureTheory.integral_add
      (phiTubeFreqLoc_norm_integrable R r hR hr hrR T₁)
      (phiTubeFreqLoc_norm_integrable R r hR hr hrR T₂)]
    exact MeasureTheory.integral_const_mul _ _

  rw [heval] at hle

  have hl1_1 := phiTubeFreqLoc_l1_le R r hR hr hrR T₁
  have hl1_2 := phiTubeFreqLoc_l1_le R r hR hr hrR T₂
  have hrinv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1:ℝ) ≤ r)
  have hRR : R * R ^ (-(1001:ℝ)) ≤ R ^ (-(1000:ℝ)) := by
    have hRp : (0:ℝ) < R := hR_pos
    have h := Real.rpow_add hRp 1 (-(1001:ℝ))
    rw [Real.rpow_one] at h
    rw [← h]
    exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 + -(1001:ℝ)) ≤ -(1000:ℝ))

  have hRnonneg : (0:ℝ) ≤ R ^ (-(1001:ℝ)) := Real.rpow_nonneg (le_of_lt hR_pos) _
  calc ∫ x, ‖phiTubeFreqLoc R r T₁ x‖ * ‖phiTubeFreqLoc R r T₂ x‖ ∂volume
      ≤ r⁻¹ * R ^ (-(1001:ℝ)) * (∫ x, ‖phiTubeFreqLoc R r T₁ x‖ ∂volume +
          ∫ x, ‖phiTubeFreqLoc R r T₂ x‖ ∂volume) := hle
    _ ≤ r⁻¹ * R ^ (-(1001:ℝ)) * (R/4 + R/4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = r⁻¹ * (R * R ^ (-(1001:ℝ))) / 2 := by ring
    _ ≤ 1 * R ^ (-(1000:ℝ)) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
        exact mul_le_mul hrinv hRR (by positivity) (by linarith)
    _ ≤ R ^ (-(1000 : ℝ)) := by linarith [Real.rpow_nonneg (le_of_lt hR_pos) (-(1000:ℝ))]

/-- Orthogonality of tube wave packets (spatial-disjointness case): if the $r$-thickenings of
$T_1$ and $T_2$ are disjoint, then $|\langle \phi_{T_1, r}, \phi_{T_2, r}\rangle| \le
R^{-1000}$. -/
theorem orthogonality_tubes_case_disjoint_support
    {R : ℝ} (hR : 1 ≤ R)
    {r : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R)
    (T₁ T₂ : Tube R)
    (hdisjoint : Disjoint (T₁.rNeighborhood r) (T₂.rNeighborhood r)) :
    ‖l2Inner (phiTubeFreqLoc R r T₁) (phiTubeFreqLoc R r T₂)‖ ≤ R ^ (-(1000 : ℝ)) := by
  unfold l2Inner
  calc ‖∫ x, phiTubeFreqLoc R r T₁ x * starRingEnd ℂ (phiTubeFreqLoc R r T₂ x) ∂volume‖
      ≤ ∫ x, ‖phiTubeFreqLoc R r T₁ x * starRingEnd ℂ (phiTubeFreqLoc R r T₂ x)‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ ≤ R ^ (-(1000 : ℝ)) :=
        phiTubeFreqLoc_product_integral_bound hR hr hrR T₁ T₂ hdisjoint

/-- Geometric covering lemma: if two tubes are angularly close ($\angle T_1, T_2 < R^\varepsilon
\cdot r/R$) and their $r$-thickenings overlap, then they fit inside a common
$R^\varepsilon r \times R^{1 + \varepsilon}$ rectangle. -/
theorem tubes_fit_in_rect_of_close
    {R : ℝ} (hR : 1 ≤ R) {r : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R)
    {ε : ℝ} (hε : 0 < ε) (T₁ T₂ : Tube R)
    (hangle : T₁.angle T₂ < R ^ ε * (r / R))
    (hoverlap : ¬Disjoint (T₁.rNeighborhood r) (T₂.rNeighborhood r)) :
    ∃ (T_tilde : Rectangle (R ^ ε * r) (R ^ (1 + ε))),
      T₁.containedIn T_tilde ∧ T₂.containedIn T_tilde := by sorry

/-- Geometric dichotomy contrapositive of `tubes_fit_in_rect_of_close`: if no common
covering $R^\varepsilon r \times R^{1 + \varepsilon}$ rectangle exists, then either the tubes
have large angular separation, or their $r$-thickenings are disjoint. -/
theorem geometric_dichotomy
    {R : ℝ} (hR : 1 ≤ R)
    {r : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R)
    {ε : ℝ} (hε : 0 < ε)
    (T₁ T₂ : Tube R)
    (hnotRect : ¬ ∃ (T_tilde : Rectangle (R ^ ε * r) (R ^ (1 + ε))),
      T₁.containedIn T_tilde ∧ T₂.containedIn T_tilde) :
    T₁.angle T₂ ≥ R ^ ε * (r / R) ∨
    Disjoint (T₁.rNeighborhood r) (T₂.rNeighborhood r) := by
  by_contra h
  push_neg at h
  obtain ⟨hangle, hnotDisjoint⟩ := h
  exact hnotRect (tubes_fit_in_rect_of_close hR hr hrR hε T₁ T₂ hangle hnotDisjoint)

/-- **Orthogonality of tube wave packets** (Lemma): if two $1 \times R$ tubes $T_1, T_2$ do
not fit into a common $R^\varepsilon r \times R^{1 + \varepsilon}$ rectangle, then
$|\langle \phi_{T_1, r}, \phi_{T_2, r}\rangle| \lesssim R^{-1000}$. The implicit constant $C$
is uniform in $R, r, T_1, T_2$. -/
theorem orthogonality_tubes
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ) (hR : 1 ≤ R) (r : ℝ) (hr : 1 ≤ r) (hrR : r ≤ R)
        (T₁ T₂ : Tube R),
      (¬ ∃ (T_tilde : Rectangle (R ^ ε * r) (R ^ (1 + ε))),
        T₁.containedIn T_tilde ∧ T₂.containedIn T_tilde) →
      ‖l2Inner (phiTubeFreqLoc R r T₁) (phiTubeFreqLoc R r T₂)‖ ≤
        C * R ^ (-(1000 : ℝ)) := by
  refine ⟨1, one_pos, ?_⟩
  intro R hR r hr hrR T₁ T₂ hnotRect

  have hdich := geometric_dichotomy hR hr hrR hε T₁ T₂ hnotRect
  rcases hdich with hangle | hdisjoint
  ·
    have h0 := orthogonality_tubes_case_angle hR hr hrR hε T₁ T₂ hangle
    simp only [h0, norm_zero, one_mul]
    exact Real.rpow_nonneg (le_trans zero_le_one hR) _
  ·
    have hbd := orthogonality_tubes_case_disjoint_support hR hr hrR T₁ T₂ hdisjoint
    linarith [Real.rpow_nonneg (le_trans zero_le_one hR) (-(1000 : ℝ))]

end OrthogonalityTubes
