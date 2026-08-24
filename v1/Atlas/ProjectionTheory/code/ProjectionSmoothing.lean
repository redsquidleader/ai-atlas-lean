/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Set Function Filter

namespace ProjectionSmoothing

/-- The projection `π_θ f : ℝ → ℂ` of an `L²` function `f : ℝ^d → ℂ` along the
direction `θ ∈ S^{d−1}`: at the point `t ∈ ℝ` it returns the integral of `f` over
the affine hyperplane `t·θ + θ^⊥`, with respect to the Haar measure on `θ^⊥`. -/
def projectionAlongDirection {d : ℕ}
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (f : EuclideanSpace ℝ (Fin d) → ℂ) : ℝ → ℂ := fun t =>
  ∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ {(θ : EuclideanSpace ℝ (Fin d))})),
    f (t • (θ : EuclideanSpace ℝ (Fin d)) + (z : EuclideanSpace ℝ (Fin d)))
    ∂Measure.addHaar

/-- The `C^k` norm of a function `g : ℝ → ℂ`: the supremum over `0 ≤ j ≤ k` and
`t ∈ ℝ` of `‖g^(j)(t)‖`. -/
def ckNorm (k : ℕ) (g : ℝ → ℂ) : ℝ :=
  ⨆ (j : Fin (k + 1)), ⨆ (t : ℝ), ‖iteratedDeriv (j : ℕ) g t‖

/-- The inhomogeneous Sobolev `H^s` squared norm `∫ (1 + |ξ|²)^s |ĝ(ξ)|² dξ`
of a function `g : ℝ → ℂ`. -/
def sobolevNormSq (s : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∫ ξ : ℝ, (1 + ‖ξ‖ ^ 2) ^ s * ‖FourierTransform.fourier g ξ‖ ^ 2

/-- **Sobolev embedding (one dimension).** If `s > 1/2 + k`, then the Sobolev
`H^s` norm controls the `C^k` norm: there is a constant `C > 0` such that
`‖g‖_{C^k}² ≤ C · ‖g‖_{H^s}²` for every `g : ℝ → ℂ`. -/
theorem sobolev_embedding (k : ℕ) (s : ℝ) (hs : s > 1 / 2 + (k : ℝ)) :
    ∃ C : ℝ, C > 0 ∧ ∀ (g : ℝ → ℂ), (ckNorm k g) ^ 2 ≤ C * sobolevNormSq s g := by sorry


/-- The homogeneous Sobolev `Ḣ^s` squared norm `∫ |ξ|^{2s} |ĝ(ξ)|² dξ`. -/
def homoSobolevNormSq (s : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∫ ξ : ℝ, ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier g ξ‖ ^ 2


/-- **Plancherel's identity on `ℝ^d`.** For `f ∈ L²(ℝ^d)`,
`∫ |f|² = ∫ |𝓕 f|²`. -/
theorem plancherel_Rd {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume =
    ∫ ξ : EuclideanSpace ℝ (Fin d), ‖FourierTransform.fourier f ξ‖ ^ 2 ∂volume := by sorry


/-- **Polar coordinate decomposition of `‖𝓕 f‖_{L²}²`.** There exists `C_d > 0`
(the polar Jacobian constant) such that
`∫ |𝓕 f|² dξ = C_d ∫_{S^{d−1}} ∫_ℝ |r|^{d−1} |𝓕 f(r θ)|² dr dσ(θ)`. -/
theorem polar_coord_integration {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    ∃ C_d : ℝ, C_d > 0 ∧
      ∫ ξ : EuclideanSpace ℝ (Fin d), ‖FourierTransform.fourier f ξ‖ ^ 2 ∂volume =
      C_d * ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        (∫ r : ℝ, ‖r‖ ^ ((d : ℝ) - 1) *
          ‖FourierTransform.fourier f (r • (θ : EuclideanSpace ℝ (Fin d)))‖ ^ 2)
        ∂(volume.toSphere) := by sorry


/-- Fubini step used in the Fourier slice theorem: rewriting the Fourier integral
of `f` against the character at `r θ` as a one-dimensional Fourier integral of
the `θ`-slice integral of `f`. -/
theorem fubini_fourier_integrand {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (r : ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin d),
      Real.fourierChar (-(innerₗ (EuclideanSpace ℝ (Fin d)) x
        (r • (θ : EuclideanSpace ℝ (Fin d))))) • f x ∂volume =
    ∫ t : ℝ, Real.fourierChar (-(innerₗ ℝ t r)) •
      (∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ
        {(θ : EuclideanSpace ℝ (Fin d))})),
        f (t • (θ : EuclideanSpace ℝ (Fin d)) +
          (z : EuclideanSpace ℝ (Fin d)))
        ∂Measure.addHaar) := by sorry

/-- **Fourier slice theorem.** For `f ∈ L²(ℝ^d)` and `θ ∈ S^{d−1}`, the 1-D Fourier
transform of the projection `π_θ f` at `r` equals the `d`-dimensional Fourier
transform of `f` evaluated at `r·θ`:
`𝓕(π_θ f)(r) = 𝓕f(r θ)`. -/
theorem fourier_slice_theorem {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (r : ℝ) :
    FourierTransform.fourier (projectionAlongDirection θ f) r =
    FourierTransform.fourier f (r • (θ : EuclideanSpace ℝ (Fin d))) := by

  simp only [FourierTransform.fourier, VectorFourier.fourierIntegral]


  rw [fubini_fourier_integrand f hf_l2 θ r]

  simp only [projectionAlongDirection]

/-- Combining polar coordinates with the Fourier slice theorem: the `L²` norm
of `𝓕 f` equals (up to a dimensional constant) the average over `θ ∈ S^{d−1}` of
the homogeneous Sobolev `Ḣ^{(d−1)/2}` squared norm of the projection `π_θ f`. -/
theorem polar_fourier_slice_identity {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    ∃ C_d : ℝ, C_d > 0 ∧
      ∫ ξ : EuclideanSpace ℝ (Fin d), ‖FourierTransform.fourier f ξ‖ ^ 2 ∂volume =
      C_d * ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        homoSobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere) := by
  obtain ⟨C_d, hC_d_pos, hpolar⟩ := polar_coord_integration f hf_l2
  refine ⟨C_d, hC_d_pos, ?_⟩
  rw [hpolar]
  congr 1; congr 1; ext θ
  simp only [homoSobolevNormSq]
  congr 1; ext r
  rw [← fourier_slice_theorem f hf_l2 θ r]
  ring_nf

/-- Bounded version: combining Plancherel on `ℝ^d` with the polar/Fourier slice
identity, the spherical average of the homogeneous Sobolev `Ḣ^{(d−1)/2}` norms of
the projections is bounded by a constant times `‖f‖_{L²}²`. -/
theorem plancherel_polar_fourier_slice_homogeneous {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    ∃ C : ℝ, C > 0 ∧
      ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        homoSobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere) ≤
      C * ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume := by

  have hplanch := plancherel_Rd f hf_l2

  obtain ⟨C_d, hC_d_pos, hpolar⟩ := polar_fourier_slice_identity f hf_l2

  refine ⟨1 / C_d, div_pos one_pos hC_d_pos, ?_⟩
  have heq : ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      homoSobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
      ∂(volume.toSphere) =
    (1 / C_d) * ∫ ξ : EuclideanSpace ℝ (Fin d),
      ‖FourierTransform.fourier f ξ‖ ^ 2 ∂volume := by
    field_simp
    linarith
  rw [heq, hplanch.symm]


/-- 1-D Plancherel for the projection: `‖𝓕(π_θ f)‖_{L²(ℝ)}² = ‖π_θ f‖_{L²(ℝ)}²`. -/
theorem projection_plancherel_1d {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2 =
      ∫ t : ℝ, ‖projectionAlongDirection θ f t‖ ^ 2 := by sorry


/-- Fubini for the projection-norm integrand: the slice integral of `‖f‖` is
integrable in `t` and its integral over `ℝ` equals `‖f‖_{L¹(ℝ^d)}`. -/
theorem fubini_projection_norm {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    Integrable (fun t : ℝ =>
      ∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ {(θ : EuclideanSpace ℝ (Fin d))})),
        ‖f (t • (θ : EuclideanSpace ℝ (Fin d)) + (z : EuclideanSpace ℝ (Fin d)))‖
        ∂Measure.addHaar) volume ∧
    ∫ t : ℝ, (∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ {(θ : EuclideanSpace ℝ (Fin d))})),
      ‖f (t • (θ : EuclideanSpace ℝ (Fin d)) + (z : EuclideanSpace ℝ (Fin d)))‖
      ∂Measure.addHaar) =
    ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume := by sorry


/-- `L¹`-bound on the projection: `‖π_θ f‖_{L¹(ℝ)} ≤ ‖f‖_{L¹(ℝ^d)}`. -/
theorem projection_l1_le_f_l1 {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ∫ t : ℝ, ‖projectionAlongDirection θ f t‖ ≤
      ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume := by

  obtain ⟨h_int, h_fubini⟩ := fubini_projection_norm f hf_l2 θ

  rw [← h_fubini]


  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun t => norm_nonneg _)
  · exact h_int
  · exact Eventually.of_forall (fun t => norm_integral_le_integral_norm _)


/-- For a nonnegative function `f`, any slice integral
`∫_{θ^⊥} f(tθ + z) dz` is bounded above by the full integral `∫_{ℝ^d} f`. -/
theorem slice_integral_le_full_integral {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (t : ℝ) :
    (∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ {(θ : EuclideanSpace ℝ (Fin d))})),
      f (t • (θ : EuclideanSpace ℝ (Fin d)) + (z : EuclideanSpace ℝ (Fin d)))
      ∂Measure.addHaar) ≤
    ∫ x : EuclideanSpace ℝ (Fin d), f x ∂volume := by sorry


/-- Pointwise `L^∞`-bound on the projection by the `L¹` norm of `f`:
`|π_θ f(t)| ≤ ‖f‖_{L¹(ℝ^d)}` for every `t`. -/
theorem projection_linfty_le_f_l1 {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (t : ℝ) :
    ‖projectionAlongDirection θ f t‖ ≤
      ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume := by
  unfold projectionAlongDirection
  calc ‖∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ {(θ : EuclideanSpace ℝ (Fin d))})),
        f (t • (θ : EuclideanSpace ℝ (Fin d)) + (z : EuclideanSpace ℝ (Fin d)))
        ∂Measure.addHaar‖
      ≤ ∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ {(θ : EuclideanSpace ℝ (Fin d))})),
        ‖f (t • (θ : EuclideanSpace ℝ (Fin d)) + (z : EuclideanSpace ℝ (Fin d)))‖
        ∂Measure.addHaar := norm_integral_le_integral_norm _
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume :=
        slice_integral_le_full_integral (fun x => ‖f x‖) (fun x => norm_nonneg _) θ t


/-- The norm `t ↦ ‖π_θ f(t)‖` of the projection is integrable on `ℝ`. -/
theorem projection_norm_integrable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    Integrable (fun t => ‖projectionAlongDirection θ f t‖) volume := by sorry

/-- `L²` Fourier bound: `‖𝓕(π_θ f)‖_{L²(ℝ)}² ≤ ‖f‖_{L¹(ℝ^d)}²`. Combines the
1-D Plancherel identity with the pointwise `L^∞` bound. -/
theorem projection_fourier_l2_le_l1_sq {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2 ≤
      (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2 := by

  rw [projection_plancherel_1d f hf_l2 θ]
  set g := projectionAlongDirection θ f
  set M := ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume
  have hM_nonneg : 0 ≤ M := integral_nonneg (fun x => norm_nonneg _)

  have h_ptwise : ∀ t : ℝ, ‖g t‖ ^ 2 ≤ M * ‖g t‖ := by
    intro t
    have h_bound := projection_linfty_le_f_l1 f hf_l2 θ t
    calc ‖g t‖ ^ 2 = ‖g t‖ * ‖g t‖ := sq (‖g t‖)
      _ ≤ M * ‖g t‖ := by gcongr

  calc ∫ t : ℝ, ‖g t‖ ^ 2
      ≤ ∫ t : ℝ, M * ‖g t‖ := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall (fun t => by positivity)
        · exact (projection_norm_integrable f hf_l2 θ).const_mul M
        · exact Eventually.of_forall h_ptwise
    _ = M * ∫ t : ℝ, ‖g t‖ := integral_const_mul M _
    _ ≤ M * M := by gcongr; exact projection_l1_le_f_l1 f hf_l2 θ
    _ = M ^ 2 := (sq M).symm

/-- Low-frequency bound: the spherical average of `∫ |𝓕(π_θ f)|²` is bounded
by a constant times `‖f‖_{L¹(ℝ^d)}²`. -/
theorem fourier_slice_low_freq_bound {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    ∃ C : ℝ, C > 0 ∧
      ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        (∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2)
        ∂(volume.toSphere) ≤
      C * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2 := by
  set M := (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2
  set μ := (volume.toSphere : Measure (↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1)))

  set A := (μ Set.univ).toReal

  refine ⟨max 1 A, lt_max_of_lt_left one_pos, ?_⟩

  calc ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        (∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2)
        ∂μ
      ≤ ∫ _ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1), M ∂μ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Eventually.of_forall (fun _ => by positivity)
        · exact integrable_const M
        · exact Eventually.of_forall (fun θ => projection_fourier_l2_le_l1_sq f hf_l2 θ)
    _ = A * M := by
        rw [integral_const, smul_eq_mul]; rfl
    _ ≤ max 1 A * M := by
        gcongr
        exact le_max_right 1 A

/-- The Sobolev squared norm is nonnegative. -/
lemma sobolevNormSq_nonneg (s : ℝ) (g : ℝ → ℂ) : 0 ≤ sobolevNormSq s g := by
  apply integral_nonneg
  intro ξ
  positivity


/-- The map `θ ↦ ∫ |𝓕(π_θ f)|²` is `AEStronglyMeasurable` on `S^{d−1}`. -/
theorem projection_fourier_l2_aestronglymeasurable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    AEStronglyMeasurable (fun θ => ∫ ξ : ℝ,
      ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2)
      volume.toSphere := by sorry

/-- The map `θ ↦ ∫ |𝓕(π_θ f)|²` is integrable on `S^{d−1}`. -/
theorem projection_fourier_l2_integrable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    Integrable (fun θ => ∫ ξ : ℝ,
      ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2)
      volume.toSphere := by
  apply Integrable.of_bound (projection_fourier_l2_aestronglymeasurable f hf_l2)
    ((∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2)
  filter_upwards with θ
  rw [Real.norm_of_nonneg (by positivity)]
  exact projection_fourier_l2_le_l1_sq f hf_l2 θ


/-- The map `θ ↦ ‖π_θ f‖_{Ḣ^{(d−1)/2}}²` is `AEStronglyMeasurable` on `S^{d−1}`. -/
theorem projection_homo_sobolev_aestronglymeasurable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    AEStronglyMeasurable (fun θ => homoSobolevNormSq (((d : ℝ) - 1) / 2)
        (projectionAlongDirection θ f)) volume.toSphere := by sorry


/-- The map `θ ↦ ‖π_θ f‖_{Ḣ^{(d−1)/2}}²` has finite integral on `S^{d−1}`. -/
theorem projection_homo_sobolev_hasFiniteIntegral {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    HasFiniteIntegral (fun θ => homoSobolevNormSq (((d : ℝ) - 1) / 2)
        (projectionAlongDirection θ f)) volume.toSphere := by sorry

/-- The map `θ ↦ ‖π_θ f‖_{Ḣ^{(d−1)/2}}²` is integrable on `S^{d−1}`. -/
theorem projection_homo_sobolev_integrable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    Integrable (fun θ => homoSobolevNormSq (((d : ℝ) - 1) / 2)
        (projectionAlongDirection θ f)) volume.toSphere :=
  ⟨projection_homo_sobolev_aestronglymeasurable f hf_l2,
   projection_homo_sobolev_hasFiniteIntegral f hf_l2⟩


/-- Auxiliary integrability statement used in `sobolev_norm_split`: integrability
of the `(1+|ξ|²)^s · |ĝ|²` integrand transfers to the majorant
`2^{|s|}(|ĝ|² + |ξ|^{2s}|ĝ|²)`. -/
theorem sobolev_split_integrability (s : ℝ) (g : ℝ → ℂ)
    (hf : Integrable (fun ξ : ℝ => (1 + ‖ξ‖ ^ 2) ^ s *
      ‖FourierTransform.fourier g ξ‖ ^ 2) volume) :
    Integrable (fun ξ : ℝ => 2 ^ |s| * (‖FourierTransform.fourier g ξ‖ ^ 2 +
      ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier g ξ‖ ^ 2)) volume := by sorry


/-- Splitting the integral of `|ĝ|² + |ξ|^{2s}|ĝ|²` as the sum of two integrals,
given integrability of the joint integrand. -/
theorem sobolev_split_integral_add (s : ℝ) (g : ℝ → ℂ)
    (hh : Integrable (fun ξ : ℝ => 2 ^ |s| * (‖FourierTransform.fourier g ξ‖ ^ 2 +
      ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier g ξ‖ ^ 2)) volume) :
    (∫ ξ : ℝ, (‖FourierTransform.fourier g ξ‖ ^ 2 +
      ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier g ξ‖ ^ 2)) =
    (∫ ξ : ℝ, ‖FourierTransform.fourier g ξ‖ ^ 2) +
      ∫ ξ : ℝ, ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier g ξ‖ ^ 2 := by sorry

/-- Pointwise control of the inhomogeneous Sobolev norm by the `L²` and homogeneous
Sobolev parts: `‖g‖_{H^s}² ≤ 2^{|s|}(‖ĝ‖_{L²}² + ‖g‖_{Ḣ^s}²)`. -/
theorem sobolev_norm_split (s : ℝ) (g : ℝ → ℂ) :
    sobolevNormSq s g ≤ 2 ^ |s| *
      ((∫ ξ : ℝ, ‖FourierTransform.fourier g ξ‖ ^ 2) + homoSobolevNormSq s g) := by
  unfold sobolevNormSq homoSobolevNormSq
  set ĝ := FourierTransform.fourier g
  set f := fun ξ : ℝ => (1 + ‖ξ‖ ^ 2) ^ s * ‖ĝ ξ‖ ^ 2
  set h := fun ξ : ℝ => 2 ^ |s| * (‖ĝ ξ‖ ^ 2 + ‖ξ‖ ^ (2 * s) * ‖ĝ ξ‖ ^ 2)

  have hfh : ∀ ξ, f ξ ≤ h ξ := by
    intro ξ; simp only [f, h]
    have hpw : (1 + ‖ξ‖ ^ 2) ^ s ≤ 2 ^ |s| * (1 + ‖ξ‖ ^ (2 * s)) := by
      have hx := norm_nonneg ξ
      rcases le_or_gt 0 s with hs | hs
      · rw [abs_of_nonneg hs]
        calc (1 + ‖ξ‖ ^ 2) ^ s
            ≤ (2 * max 1 (‖ξ‖ ^ 2)) ^ s :=
              Real.rpow_le_rpow (by positivity)
                (by linarith [le_max_left (1:ℝ) (‖ξ‖^2), le_max_right (1:ℝ) (‖ξ‖^2)]) hs
          _ = 2 ^ s * (max 1 (‖ξ‖ ^ 2)) ^ s :=
              Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)
          _ ≤ 2 ^ s * (1 + ‖ξ‖ ^ (2 * s)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) s)
              rcases le_or_gt (‖ξ‖ ^ 2) 1 with hle | hgt
              · rw [max_eq_left hle, Real.one_rpow]
                linarith [Real.rpow_nonneg hx (2*s)]
              · rw [max_eq_right hgt.le]
                have : (‖ξ‖^2 : ℝ)^s = ‖ξ‖^(2*s) := by
                  rw [← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul hx]; ring_nf
                linarith [this.symm ▸ le_refl (‖ξ‖^(2*s))]
      · calc (1 + ‖ξ‖ ^ 2) ^ s
            ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg ‖ξ‖]) hs.le
          _ ≤ 2 ^ |s| * (1 + ‖ξ‖ ^ (2 * s)) := by
              have h3 : (1:ℝ) ≤ 2^|s| := by
                calc (1:ℝ) = 2^(0:ℝ) := by simp
                  _ ≤ 2^|s| := Real.rpow_le_rpow_of_exponent_le (by norm_num) (abs_nonneg s)
              linarith [Real.rpow_nonneg hx (2*s),
                mul_le_mul h3 (show (1:ℝ) ≤ 1 + ‖ξ‖^(2*s) from by
                  linarith [Real.rpow_nonneg hx (2*s)]) (by linarith) (by positivity)]
    calc (1 + ‖ξ‖^2)^s * ‖ĝ ξ‖^2
        ≤ (2^|s| * (1 + ‖ξ‖^(2*s))) * ‖ĝ ξ‖^2 :=
          mul_le_mul_of_nonneg_right hpw (by positivity)
      _ = 2^|s| * (‖ĝ ξ‖^2 + ‖ξ‖^(2*s) * ‖ĝ ξ‖^2) := by ring

  by_cases hf_int : Integrable f volume
  · have hh_int : Integrable h volume := sobolev_split_integrability s g hf_int
    calc ∫ ξ, f ξ
        ≤ ∫ ξ, h ξ := integral_mono_of_nonneg
          (Eventually.of_forall fun ξ => by positivity)
          hh_int
          (Eventually.of_forall hfh)
      _ = 2 ^ |s| * ∫ ξ, (‖ĝ ξ‖ ^ 2 + ‖ξ‖ ^ (2 * s) * ‖ĝ ξ‖ ^ 2) :=
          integral_const_mul _ _
      _ = 2 ^ |s| * ((∫ ξ, ‖ĝ ξ‖ ^ 2) + ∫ ξ, ‖ξ‖ ^ (2 * s) * ‖ĝ ξ‖ ^ 2) := by
          congr 1; exact sobolev_split_integral_add s g hh_int
  · rw [integral_undef hf_int]
    apply mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) |s|)
    have ha : (0 : ℝ) ≤ ∫ ξ : ℝ, ‖ĝ ξ‖ ^ 2 := integral_nonneg fun ξ => by positivity
    have hb : (0 : ℝ) ≤ ∫ ξ : ℝ, ‖ξ‖ ^ (2 * s) * ‖ĝ ξ‖ ^ 2 :=
      integral_nonneg fun ξ => by positivity
    linarith

/-- The map `θ ↦ ‖π_θ f‖_{H^{(d−1)/2}}²` is `AEStronglyMeasurable` on `S^{d−1}`. -/
theorem projection_sobolev_aestronglymeasurable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    AEStronglyMeasurable (fun θ => sobolevNormSq (((d : ℝ) - 1) / 2)
        (projectionAlongDirection θ f)) volume.toSphere := by sorry

/-- The map `θ ↦ ‖π_θ f‖_{H^{(d−1)/2}}²` is integrable on `S^{d−1}`. -/
theorem projection_sobolev_integrable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    Integrable (fun θ => sobolevNormSq (((d : ℝ) - 1) / 2)
        (projectionAlongDirection θ f)) volume.toSphere := by
  set s := ((d : ℝ) - 1) / 2

  have h_bound_int : Integrable (fun θ => 2 ^ |s| *
      ((∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2) +
       homoSobolevNormSq s (projectionAlongDirection θ f))) volume.toSphere :=
    ((projection_fourier_l2_integrable f hf_l2).add
      (projection_homo_sobolev_integrable f hf_l2)).const_mul _

  exact h_bound_int.mono'
    (projection_sobolev_aestronglymeasurable f hf_l2)
    (Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sobolevNormSq_nonneg s (projectionAlongDirection θ f))]
      exact sobolev_norm_split s (projectionAlongDirection θ f))

/-- Spherical-averaged version of `sobolev_norm_split`: the average inhomogeneous
Sobolev norm of the projections is controlled by the sum of the averaged
`L²`-Fourier norm and the averaged homogeneous Sobolev norm. -/
theorem avg_sobolev_split {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        sobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere) ≤
    2 ^ |((d : ℝ) - 1) / 2| *
      (∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
          (∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2)
          ∂(volume.toSphere) +
       ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
          homoSobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
          ∂(volume.toSphere)) := by
  set s := ((d : ℝ) - 1) / 2

  have h_pointwise : ∀ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      sobolevNormSq s (projectionAlongDirection θ f) ≤
      2 ^ |s| * ((∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2) +
                  homoSobolevNormSq s (projectionAlongDirection θ f)) :=
    fun θ => sobolev_norm_split s (projectionAlongDirection θ f)

  have h_rhs_int : Integrable (fun θ => 2 ^ |s| *
      ((∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2) +
       homoSobolevNormSq s (projectionAlongDirection θ f))) volume.toSphere :=
    ((projection_fourier_l2_integrable f hf_l2).add
      (projection_homo_sobolev_integrable f hf_l2)).const_mul _

  have h_mono := MeasureTheory.integral_mono
    (projection_sobolev_integrable f hf_l2) h_rhs_int (fun θ => h_pointwise θ)

  rw [integral_const_mul, integral_add (projection_fourier_l2_integrable f hf_l2)
      (projection_homo_sobolev_integrable f hf_l2)] at h_mono
  exact h_mono

/-- Combined bound: the spherical average of `‖π_θ f‖_{H^{(d−1)/2}}²` is integrable
and bounded by a constant times `‖f‖_{L²}² + ‖f‖_{L¹}²`. -/
theorem plancherel_polar_fourier_slice_bound {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume) :
    Integrable (fun θ => sobolevNormSq (((d : ℝ) - 1) / 2)
        (projectionAlongDirection θ f)) volume.toSphere ∧
    ∃ C : ℝ, C > 0 ∧
      ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        sobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere) ≤
      C * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume +
           (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2) := by
  set s := ((d : ℝ) - 1) / 2
  refine ⟨projection_sobolev_integrable f hf_l2, ?_⟩

  obtain ⟨C₁, hC₁_pos, h_homo⟩ := plancherel_polar_fourier_slice_homogeneous f hf_l2

  obtain ⟨C₂, hC₂_pos, h_low⟩ := fourier_slice_low_freq_bound f hf_l2

  refine ⟨2 ^ |s| * max C₁ C₂, mul_pos (by positivity) (lt_max_of_lt_left hC₁_pos), ?_⟩

  calc ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        sobolevNormSq s (projectionAlongDirection θ f) ∂(volume.toSphere)

      ≤ 2 ^ |s| *
        (∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
            (∫ ξ : ℝ, ‖FourierTransform.fourier (projectionAlongDirection θ f) ξ‖ ^ 2)
            ∂(volume.toSphere) +
         ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
            homoSobolevNormSq s (projectionAlongDirection θ f)
            ∂(volume.toSphere)) := avg_sobolev_split f hf_l2

    _ ≤ 2 ^ |s| *
        (C₂ * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2 +
         C₁ * ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume) := by
        gcongr

    _ ≤ 2 ^ |s| *
        (max C₁ C₂ * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2 +
         max C₁ C₂ * ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume) := by
        gcongr
        · exact le_max_right C₁ C₂
        · exact le_max_left C₁ C₂

    _ = 2 ^ |s| * max C₁ C₂ *
        (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume +
         (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2) := by ring

/-- Cauchy–Schwarz for a function supported in the unit closed ball:
`‖f‖_{L¹}² ≤ vol(B_1) · ‖f‖_{L²}²`. -/
theorem cauchy_schwarz_compact_support {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (hf_supp : support f ⊆ closedBall 0 1) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2 ≤
      (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal *
        ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume := by

  set g : EuclideanSpace ℝ (Fin d) → ℂ := (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator (fun _ => 1)

  have h_eq : ∀ x, ‖f x‖ = ‖f x‖ * ‖g x‖ := by
    intro x
    by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
    · simp [g, indicator_of_mem hx]
    · have hx' : x ∉ support f := fun h => hx (hf_supp h)
      simp [mem_support] at hx'
      rw [hx', norm_zero, zero_mul]

  have h_holder : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num

  have hf_memLp : MemLp f (ENNReal.ofReal 2) volume := by
    rwa [show ENNReal.ofReal (2 : ℝ) = 2 from by simp [ENNReal.ofReal]]

  have hg_memLp : MemLp g (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 from by simp [ENNReal.ofReal]]
    exact memLp_indicator_const 2 measurableSet_closedBall 1
      (Or.inr measure_closedBall_lt_top.ne)

  have h_ineq := integral_mul_norm_le_Lp_mul_Lq h_holder hf_memLp hg_memLp

  have h_g_integral : ∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖ ^ (2 : ℝ) ∂volume =
      (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal := by
    have h1 : (fun x => ‖g x‖ ^ (2 : ℝ)) = (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator (fun _ => (1 : ℝ)) := by
      ext x
      by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
      · simp [g, indicator_of_mem hx]
      · simp [g, indicator_of_notMem hx, norm_zero,
              Real.zero_rpow (show (2:ℝ) ≠ 0 from by norm_num)]
    rw [h1, integral_indicator measurableSet_closedBall, integral_const]
    simp [Measure.real]

  suffices h : (∫ x, ‖f x‖ ∂volume) ^ 2 ≤
      (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal *
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume by
    convert h using 2
    congr 1; ext x; norm_cast

  rw [show ∫ x, ‖f x‖ ∂volume = ∫ x, ‖f x‖ * ‖g x‖ ∂volume from by
    congr 1; ext x; exact h_eq x]

  have h_f_int_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ (2 : ℝ) ∂volume :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have h_g_int_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖ ^ (2 : ℝ) ∂volume :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have h_product_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ * ‖g x‖ ∂volume :=
    integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))

  calc (∫ x, ‖f x‖ * ‖g x‖ ∂volume) ^ 2
      ≤ ((∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2) * (∫ x, ‖g x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2)) ^ 2 := by
        apply sq_le_sq' (by linarith) h_ineq
    _ = (∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) * (∫ x, ‖g x‖ ^ (2:ℝ) ∂volume) := by
        rw [mul_pow, ← Real.rpow_natCast ((∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2)) 2,
            ← Real.rpow_natCast ((∫ x, ‖g x‖ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2)) 2,
            ← Real.rpow_mul h_f_int_nonneg, ← Real.rpow_mul h_g_int_nonneg]
        norm_num
    _ = (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal *
          (∫ x, ‖f x‖ ^ (2:ℝ) ∂volume) := by
        rw [h_g_integral]; ring

/-- For `f ∈ L²(ℝ^d)` supported in the unit ball, the spherical average of
`‖π_θ f‖_{H^{(d−1)/2}}²` is controlled by a constant times `‖f‖_{L²}²`. -/
theorem avg_sobolev_norm_projection_bound {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (hf_supp : support f ⊆ closedBall 0 1) :
    ∃ C : ℝ, C > 0 ∧
      Integrable (fun θ => sobolevNormSq (((d : ℝ) - 1) / 2)
          (projectionAlongDirection θ f)) volume.toSphere ∧
      ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        sobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere) ≤
      C * ∫ x, ‖f x‖ ^ 2 ∂volume := by


  obtain ⟨hint, C₁, hC₁_pos, hbound⟩ := plancherel_polar_fourier_slice_bound f hf_l2

  have hcs := cauchy_schwarz_compact_support f hf_l2 hf_supp
  set V := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
  have hV_nonneg : (0 : ℝ) ≤ V := ENNReal.toReal_nonneg

  refine ⟨C₁ * (1 + V), mul_pos hC₁_pos (by linarith), hint, ?_⟩
  calc ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        sobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere)
      ≤ C₁ * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume +
           (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ∂volume) ^ 2) := hbound
    _ ≤ C₁ * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume +
           V * ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume) := by
        gcongr
    _ = C₁ * (1 + V) * ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 ∂volume := by ring

/-- **Theorem 6.1 (Projection smoothing).** If `f ∈ L²(ℝ^d)` is supported in the
unit ball and `(d−1)/2 > 1/2 + k`, then
$$\int_{S^{d-1}} \|\pi_\theta f\|_{C^k}^2\, d\theta \lesssim \|f\|_{L^2}^2.$$
Projection along a random direction `θ` smooths an `L²` function into a `C^k`
function on average. -/
theorem smoothing_by_projection {d : ℕ} (k : ℕ)
    (hdim : ((d : ℝ) - 1) / 2 > 1 / 2 + (k : ℝ))
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf_l2 : MemLp f 2 volume)
    (hf_supp : support f ⊆ closedBall 0 1) :
    ∃ C : ℝ, C > 0 ∧
      ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        (ckNorm k (projectionAlongDirection θ f)) ^ 2
        ∂(volume.toSphere) ≤
      C * ∫ x, ‖f x‖ ^ 2 ∂volume := by

  obtain ⟨C_emb, hC_emb_pos, hC_emb⟩ := sobolev_embedding k (((d : ℝ) - 1) / 2) hdim

  obtain ⟨C_avg, hC_avg_pos, hC_avg_int, hC_avg⟩ :=
    avg_sobolev_norm_projection_bound f hf_l2 hf_supp

  refine ⟨C_emb * C_avg, mul_pos hC_emb_pos hC_avg_pos, ?_⟩
  have hint : Integrable (fun θ => C_emb * sobolevNormSq (((d : ℝ) - 1) / 2)
      (projectionAlongDirection θ f)) volume.toSphere :=
    hC_avg_int.const_mul C_emb
  calc ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        (ckNorm k (projectionAlongDirection θ f)) ^ 2
        ∂(volume.toSphere)
      ≤ ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        C_emb * sobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Eventually.of_forall (fun θ => by positivity)
          · exact hint
          · exact Eventually.of_forall (fun θ => hC_emb _)
    _ = C_emb * ∫ θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        sobolevNormSq (((d : ℝ) - 1) / 2) (projectionAlongDirection θ f)
        ∂(volume.toSphere) := by
          rw [integral_const_mul]
    _ ≤ C_emb * (C_avg * ∫ x, ‖f x‖ ^ 2 ∂volume) := by
          apply mul_le_mul_of_nonneg_left hC_avg (le_of_lt hC_emb_pos)
    _ = C_emb * C_avg * ∫ x, ‖f x‖ ^ 2 ∂volume := by ring

end ProjectionSmoothing
