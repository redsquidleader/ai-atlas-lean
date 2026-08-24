/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.HodgeStarMathlib

open scoped Manifold ComplexConjugate
open MeasureTheory
set_option autoImplicit false

noncomputable section

namespace L2AdjointnessMathlib

open HodgeStarMathlib

/-- The Dolbeault operator $\bar\partial : \Omega^{p,q}(M) \to \Omega^{p,q+1}(M)$ on a complex
manifold $M$, here applied to smooth forms of total degree $k$, producing one of degree $k+1$. -/
noncomputable def delbar {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    SmoothForm n M k → SmoothForm n M (k + 1) := by sorry


/-- The Dolbeault operator squares to zero: $\bar\partial^2 = 0$. -/
theorem delbar_sq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) :
    @delbar n M _ _ _ (k + 1) (@delbar n M _ _ _ k α) = 0 := by sorry

/-- Additivity of $\bar\partial$: $\bar\partial(\alpha + \beta) = \bar\partial\alpha + \bar\partial\beta$. -/
theorem delbar_add {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α β : SmoothForm n M k) :
    @delbar n M _ _ _ k (α + β) = @delbar n M _ _ _ k α + @delbar n M _ _ _ k β := by sorry

/-- $\mathbb{C}$-linearity of $\bar\partial$: $\bar\partial(c \cdot \alpha) = c \cdot \bar\partial\alpha$. -/
theorem delbar_smul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (c : ℂ) (α : SmoothForm n M k) :
    @delbar n M _ _ _ k (c • α) = c • @delbar n M _ _ _ k α := by sorry

/-- The formal adjoint $\bar\partial^*$ of the Dolbeault operator with respect to the $L^2$
inner product, lowering the form degree from $k+1$ to $k$. -/
noncomputable def delbar_star {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    SmoothForm n M (k + 1) → SmoothForm n M k := by sorry


/-- Additivity of $\bar\partial^*$: $\bar\partial^*(\alpha + \beta) = \bar\partial^*\alpha + \bar\partial^*\beta$. -/
theorem delbar_star_add {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α β : SmoothForm n M (k + 1)) :
    @delbar_star n M _ _ _ k (α + β) =
      @delbar_star n M _ _ _ k α + @delbar_star n M _ _ _ k β := by sorry

/-- $\mathbb{C}$-linearity of $\bar\partial^*$: $\bar\partial^*(c \cdot \alpha) = c \cdot \bar\partial^* \alpha$. -/
theorem delbar_star_smul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (c : ℂ) (α : SmoothForm n M (k + 1)) :
    @delbar_star n M _ _ _ k (c • α) = c • @delbar_star n M _ _ _ k α := by sorry

/-- The holomorphic Dolbeault operator $\partial : \Omega^{p,q}(M) \to \Omega^{p+1,q}(M)$ on
a complex manifold, increasing the total degree by one. -/
noncomputable def del {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    SmoothForm n M k → SmoothForm n M (k + 1) := by sorry

/-- The formal $L^2$-adjoint $\partial^*$ of the operator $\partial$, lowering the form degree
from $k+1$ to $k$. -/
noncomputable def del_star {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    SmoothForm n M (k + 1) → SmoothForm n M k := by sorry

/-- Stokes' theorem for $\bar\partial$ on a compact complex manifold $M$ (without boundary):
the integral $\int_M \bar\partial \omega = 0$ for any smooth form $\omega$ of top-1 degree. -/
theorem stokes_delbar {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M]
    (μ : Measure M)
    {k : ℕ} (ω : SmoothForm n M k) :
    integrateScalar μ (fun x => (@delbar n M _ _ _ k ω) x (fun _ => 0)) = 0 := by sorry

/-- The Leibniz rule for $\bar\partial$ applied pointwise to a wedge product
$\alpha \wedge (*\bar\beta)$: $\bar\partial(\alpha \wedge *\bar\beta) =
\bar\partial\alpha \wedge *\bar\beta + (-1)^k \alpha \wedge \bar\partial(*\bar\beta)$. -/
theorem delbar_leibniz_pointwise {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) (x : M) :
    (@delbar n M _ _ _ (k + (2 * n - (k + 1)))
      (@wedgeProduct n M _ k (2 * n - (k + 1)) α
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) =
    (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
      (@delbar n M _ _ _ k α)
      (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) +
    ((-1 : ℂ) ^ k) *
    (@wedgeProduct n M _ k ((2 * n - (k + 1)) + 1) α
      (@delbar n M _ _ _ (2 * n - (k + 1))
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) := by sorry

/-- Sign formula relating the second term in the Leibniz expansion to the formal adjoint:
$(-1)^k \alpha \wedge \bar\partial(*\bar\beta) = -\alpha \wedge *\overline{\bar\partial^* \beta}$,
the algebraic identity underlying the construction of $\bar\partial^*$. -/
theorem delbar_star_sign_formula {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) (x : M) :
    ((-1 : ℂ) ^ k) *
    (@wedgeProduct n M _ k ((2 * n - (k + 1)) + 1) α
      (@delbar n M _ _ _ (2 * n - (k + 1))
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) =
    -((@wedgeProduct n M _ k (2 * n - k) α
      (@hodgeStar n M _ k (@conjForm n M _ k (@delbar_star n M _ _ _ k β)))) x
      (fun _ => 0)) := by sorry

/-- The pointwise scalar associated with a wedge product of smooth forms on a compact manifold
is integrable with respect to any measure $\mu$. -/
theorem smooth_form_integrable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M]
    (μ : Measure M) {k l : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M l) :
    Integrable (fun x => (@wedgeProduct n M _ k l α β) x (fun _ => 0)) μ := by sorry

/-- Stokes' theorem for $\partial$ on a compact complex manifold $M$ (without boundary):
$\int_M \partial \omega = 0$ for any smooth form $\omega$. -/
theorem stokes_del {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M]
    (μ : Measure M)
    {k : ℕ} (ω : SmoothForm n M k) :
    integrateScalar μ (fun x => (@del n M _ _ _ k ω) x (fun _ => 0)) = 0 := by sorry

/-- The Leibniz rule for $\partial$ applied pointwise to the wedge product $\alpha \wedge *\bar\beta$,
splitting into $\partial\alpha \wedge *\bar\beta + (-1)^k \alpha \wedge \partial(*\bar\beta)$. -/
theorem del_leibniz_pointwise {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) (x : M) :
    (@del n M _ _ _ (k + (2 * n - (k + 1)))
      (@wedgeProduct n M _ k (2 * n - (k + 1)) α
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) =
    (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
      (@del n M _ _ _ k α)
      (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) +
    ((-1 : ℂ) ^ k) *
    (@wedgeProduct n M _ k ((2 * n - (k + 1)) + 1) α
      (@del n M _ _ _ (2 * n - (k + 1))
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) := by sorry

/-- Sign formula relating the Leibniz remainder $(-1)^k \alpha \wedge \partial(*\bar\beta)$ to
$-\alpha \wedge *\overline{\partial^* \beta}$, the algebraic identity behind $\partial^*$. -/
theorem del_star_sign_formula {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) (x : M) :
    ((-1 : ℂ) ^ k) *
    (@wedgeProduct n M _ k ((2 * n - (k + 1)) + 1) α
      (@del n M _ _ _ (2 * n - (k + 1))
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) =
    -((@wedgeProduct n M _ k (2 * n - k) α
      (@hodgeStar n M _ k (@conjForm n M _ k (@del_star n M _ _ _ k β)))) x
      (fun _ => 0)) := by sorry

/-- Pointwise identity combining the Leibniz rule and the sign formula:
$\bar\partial(\alpha \wedge *\bar\beta) = \bar\partial\alpha \wedge *\bar\beta -
\alpha \wedge *\overline{\bar\partial^* \beta}$. -/
theorem delbar_integrand_identity {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) (x : M) :
    (@delbar n M _ _ _ (k + (2 * n - (k + 1)))
      (@wedgeProduct n M _ k (2 * n - (k + 1)) α
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) =
    (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
      (@delbar n M _ _ _ k α)
      (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) -
    (@wedgeProduct n M _ k (2 * n - k) α
      (@hodgeStar n M _ k (@conjForm n M _ k (@delbar_star n M _ _ _ k β)))) x
      (fun _ => 0) := by

  have h_leibniz := delbar_leibniz_pointwise α β x

  have h_sign := delbar_star_sign_formula α β x


  rw [h_leibniz, h_sign]
  ring

/-- The $L^2$ adjointness defect of $\bar\partial$ and $\bar\partial^*$ equals an exact boundary
integral: $\langle \bar\partial\alpha, \beta \rangle_{L^2} - \langle \alpha, \bar\partial^* \beta \rangle_{L^2}
= \int_M \bar\partial(\alpha \wedge *\bar\beta)$. -/
theorem delbar_L2_diff_eq_boundary {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M]
    (μ : Measure M) {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) :
    L2InnerProduct μ (@delbar n M _ _ _ k α) β -
      L2InnerProduct μ α (@delbar_star n M _ _ _ k β) =
    integrateScalar μ (fun x =>
      (@delbar n M _ _ _ (k + (2 * n - (k + 1)))
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0)) := by


  have h_eq : (fun x =>
      (@delbar n M _ _ _ (k + (2 * n - (k + 1)))
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0)) =
    (fun x =>
      (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
        (@delbar n M _ _ _ k α)
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) -
      (@wedgeProduct n M _ k (2 * n - k) α
        (@hodgeStar n M _ k (@conjForm n M _ k (@delbar_star n M _ _ _ k β)))) x
        (fun _ => 0)) := by
    funext x
    exact delbar_integrand_identity α β x

  rw [show integrateScalar μ (fun x =>
      (@delbar n M _ _ _ (k + (2 * n - (k + 1)))
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0)) =
    integrateScalar μ (fun x =>
      (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
        (@delbar n M _ _ _ k α)
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) -
      (@wedgeProduct n M _ k (2 * n - k) α
        (@hodgeStar n M _ k (@conjForm n M _ k (@delbar_star n M _ _ _ k β)))) x
        (fun _ => 0)) from congrArg (integrateScalar μ) h_eq]

  exact (integral_sub
    (smooth_form_integrable μ (@delbar n M _ _ _ k α)
      (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))
    (smooth_form_integrable μ α
      (@hodgeStar n M _ k (@conjForm n M _ k (@delbar_star n M _ _ _ k β))))).symm

/-- Pointwise identity combining the Leibniz rule and the sign formula for $\partial$:
$\partial(\alpha \wedge *\bar\beta) = \partial\alpha \wedge *\bar\beta -
\alpha \wedge *\overline{\partial^* \beta}$. -/
theorem del_integrand_identity {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) (x : M) :
    (@del n M _ _ _ (k + (2 * n - (k + 1)))
      (@wedgeProduct n M _ k (2 * n - (k + 1)) α
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0) =
    (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
      (@del n M _ _ _ k α)
      (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) -
    (@wedgeProduct n M _ k (2 * n - k) α
      (@hodgeStar n M _ k (@conjForm n M _ k (@del_star n M _ _ _ k β)))) x
      (fun _ => 0) := by
  have h_leibniz := del_leibniz_pointwise α β x
  have h_sign := del_star_sign_formula α β x
  rw [h_leibniz, h_sign]
  ring

/-- The $L^2$ adjointness defect of $\partial$ and $\partial^*$ equals an exact boundary
integral: $\langle \partial\alpha, \beta \rangle_{L^2} - \langle \alpha, \partial^* \beta \rangle_{L^2}
= \int_M \partial(\alpha \wedge *\bar\beta)$. -/
theorem del_L2_diff_eq_boundary {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M]
    (μ : Measure M) {k : ℕ}
    (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)) :
    L2InnerProduct μ (@del n M _ _ _ k α) β -
      L2InnerProduct μ α (@del_star n M _ _ _ k β) =
    integrateScalar μ (fun x =>
      (@del n M _ _ _ (k + (2 * n - (k + 1)))
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0)) := by
  have h_eq : (fun x =>
      (@del n M _ _ _ (k + (2 * n - (k + 1)))
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0)) =
    (fun x =>
      (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
        (@del n M _ _ _ k α)
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) -
      (@wedgeProduct n M _ k (2 * n - k) α
        (@hodgeStar n M _ k (@conjForm n M _ k (@del_star n M _ _ _ k β)))) x
        (fun _ => 0)) := by
    funext x
    exact del_integrand_identity α β x
  rw [show integrateScalar μ (fun x =>
      (@del n M _ _ _ (k + (2 * n - (k + 1)))
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))) x (fun _ => 0)) =
    integrateScalar μ (fun x =>
      (@wedgeProduct n M _ (k + 1) (2 * n - (k + 1))
        (@del n M _ _ _ k α)
        (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β))) x (fun _ => 0) -
      (@wedgeProduct n M _ k (2 * n - k) α
        (@hodgeStar n M _ k (@conjForm n M _ k (@del_star n M _ _ _ k β)))) x
        (fun _ => 0)) from congrArg (integrateScalar μ) h_eq]
  exact (integral_sub
    (smooth_form_integrable μ (@del n M _ _ _ k α)
      (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))
    (smooth_form_integrable μ α
      (@hodgeStar n M _ k (@conjForm n M _ k (@del_star n M _ _ _ k β))))).symm


/-- $L^2$ adjointness of the Dolbeault operators: on a compact complex manifold $M$,
$\bar\partial^*$ is the $L^2$-adjoint of $\bar\partial$ and $\partial^*$ is the $L^2$-adjoint
of $\partial$, i.e. $\langle \bar\partial\alpha, \beta\rangle = \langle\alpha, \bar\partial^*\beta\rangle$
and $\langle \partial\alpha, \beta\rangle = \langle\alpha, \partial^*\beta\rangle$. -/
theorem lemma2_L2_adjointness
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M]
    (μ : Measure M) {k : ℕ} :

    (∀ (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)),
      L2InnerProduct μ (@delbar n M _ _ _ k α) β =
        L2InnerProduct μ α (@delbar_star n M _ _ _ k β)) ∧

    (∀ (α : SmoothForm n M k) (β : SmoothForm n M (k + 1)),
      L2InnerProduct μ (@del n M _ _ _ k α) β =
        L2InnerProduct μ α (@del_star n M _ _ _ k β)) := by
  constructor
  ·
    intro α β

    have h_diff := delbar_L2_diff_eq_boundary μ α β

    have h_stokes := stokes_delbar μ
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))

    have h_zero : L2InnerProduct μ (@delbar n M _ _ _ k α) β -
        L2InnerProduct μ α (@delbar_star n M _ _ _ k β) = 0 := by
      rw [h_diff, h_stokes]
    exact sub_eq_zero.mp h_zero
  ·
    intro α β
    have h_diff := del_L2_diff_eq_boundary μ α β
    have h_stokes := stokes_del μ
        (@wedgeProduct n M _ k (2 * n - (k + 1)) α
          (@hodgeStar n M _ (k + 1) (@conjForm n M _ (k + 1) β)))
    have h_zero : L2InnerProduct μ (@del n M _ _ _ k α) β -
        L2InnerProduct μ α (@del_star n M _ _ _ k β) = 0 := by
      rw [h_diff, h_stokes]
    exact sub_eq_zero.mp h_zero

/-- The Dolbeault Laplacian (or $\bar\partial$-Laplacian)
$\Delta_{\bar\partial} = \bar\partial \bar\partial^* + \bar\partial^* \bar\partial$
acting on smooth $(p,q)$-forms. -/
def dolbeaultLaplacian {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M (k + 1)) : SmoothForm n M (k + 1) :=
  @delbar n M _ _ _ k (@delbar_star n M _ _ _ k α) +
    @delbar_star n M _ _ _ (k + 1) (@delbar n M _ _ _ (k + 1) α)

end L2AdjointnessMathlib

end
