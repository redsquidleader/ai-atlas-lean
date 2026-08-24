/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.BilinearForm

set_option maxHeartbeats 0

namespace Garrett

variable {k : Type*} [Field k]


/-- The orthogonal direct sum of two bilinear forms `B₁` on `V₁` and `B₂` on `V₂`,
defined on the product space by `(p, q) ↦ B₁ p.1 q.1 + B₂ p.2 q.2`. -/
noncomputable def BilinForm.orthogonalSum {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂) :
    LinearMap.BilinForm k (V₁ × V₂) :=
  LinearMap.mk₂ k (fun p q => B₁ p.1 q.1 + B₂ p.2 q.2)
    (by intro x y z; simp [map_add, LinearMap.add_apply]; ring)
    (by intro c x y; simp [map_smul, LinearMap.smul_apply]; ring)
    (by intro x y z; simp [map_add]; ring)
    (by intro c x y; simp; ring)

/-- Evaluation formula for the orthogonal direct sum of bilinear forms. -/
@[simp]
lemma BilinForm.orthogonalSum_apply {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (v w : V₁ × V₂) :
    BilinForm.orthogonalSum B₁ B₂ v w = B₁ v.1 w.1 + B₂ v.2 w.2 := by
  simp [BilinForm.orthogonalSum, LinearMap.mk₂]

/-- Negation distributes over the orthogonal direct sum of bilinear forms. -/
lemma neg_orthogonalSum_eq {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂) :
    -(BilinForm.orthogonalSum B₁ B₂) = BilinForm.orthogonalSum (-B₁) (-B₂) := by
  ext v w
  all_goals simp [BilinForm.orthogonalSum, LinearMap.mk₂, LinearMap.neg_apply, map_zero,
    LinearMap.zero_apply]

/-- A bilinear form is nondegenerate (in the orthogonal-complement sense) when
the orthogonal complement of the whole space is trivial. -/
def BilinForm.IsNondegenerate' {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥

/-- A bilinear form `B` is hyperbolic if it is nondegenerate and admits a
Lagrangian subspace `W` (a totally isotropic subspace equal to its own orthogonal
complement). -/
def BilinForm.IsHyperbolic {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  ∃ (W : Submodule k V),
    (∀ w₁ ∈ W, ∀ w₂ ∈ W, B w₁ w₂ = 0) ∧
    LinearMap.BilinForm.orthogonal B W = W ∧
    BilinForm.IsNondegenerate' B

/-- A linear equivalence `φ : V₁ ≃ₗ V₂` is an isometry of formed spaces if it
preserves the corresponding bilinear forms `B₁` and `B₂`. -/
def IsFormedSpaceIsometry {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (φ : V₁ ≃ₗ[k] V₂) : Prop :=
  ∀ v w : V₁, B₂ (φ v) (φ w) = B₁ v w

/-- Two formed spaces `(V₁, B₁)` and `(V₂, B₂)` are isometric if there exists a
linear equivalence between them preserving the bilinear forms. -/
def FormedSpacesIsometric {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂) : Prop :=
  ∃ φ : V₁ ≃ₗ[k] V₂, IsFormedSpaceIsometry B₁ B₂ φ


/-- The orthogonal direct sum of two nondegenerate bilinear forms is
nondegenerate. -/
theorem orthogonalSum_nondegenerate
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (h₁ : BilinForm.IsNondegenerate' B₁) (h₂ : BilinForm.IsNondegenerate' B₂) :
    BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B₁ B₂) := by
  rw [BilinForm.IsNondegenerate'] at *; rw [Submodule.eq_bot_iff] at *
  intro ⟨v₁, v₂⟩ hv; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
  have hv1 : v₁ = 0 := by
    apply h₁; rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro w _
    have := hv (w, 0) Submodule.mem_top
    unfold LinearMap.BilinForm.IsOrtho at this; simp at this; exact this
  have hv2 : v₂ = 0 := by
    apply h₂; rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro w _
    have := hv (0, w) Submodule.mem_top
    unfold LinearMap.BilinForm.IsOrtho at this; simp at this; exact this
  simp [hv1, hv2]

/-- The negation of a nondegenerate bilinear form is nondegenerate. -/
theorem neg_nondegenerate {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hnd : BilinForm.IsNondegenerate' B) :
    BilinForm.IsNondegenerate' (-B) := by
  rw [BilinForm.IsNondegenerate'] at *; rw [Submodule.eq_bot_iff] at *
  intro v hv; apply hnd; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro w hw; have := hv w hw
  unfold LinearMap.BilinForm.IsOrtho at this ⊢; simp at this; exact this

/-- The diagonal subspace `{(v, v) | v ∈ V}` of `V × V`. -/
def diagonal (V : Type*) [AddCommGroup V] [Module k V] : Submodule k (V × V) where
  carrier := {p | p.1 = p.2}
  add_mem' := by intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ (ha : a₁ = a₂) (hb : b₁ = b₂); simp [ha, hb]
  zero_mem' := rfl
  smul_mem' := by intro c ⟨a₁, a₂⟩ (ha : a₁ = a₂); simp [ha]

/-- For any nondegenerate bilinear form `B`, the orthogonal direct sum
`B ⊕ (-B)` is hyperbolic, with Lagrangian given by the diagonal subspace. -/
theorem directSum_neg_isHyperbolic
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hnd : BilinForm.IsNondegenerate' B) :
    BilinForm.IsHyperbolic (BilinForm.orthogonalSum B (-B)) := by
  refine ⟨diagonal V, ?_, ?_, ?_⟩
  ·
    intro ⟨w₁, w₂⟩ (hw : w₁ = w₂) ⟨u₁, u₂⟩ (hu : u₁ = u₂)
    simp [hw, hu]
  ·
    ext ⟨a, b⟩
    simp only [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro ha
      show a = b
      have hab : a - b = 0 := by
        rw [BilinForm.IsNondegenerate'] at hnd
        rw [Submodule.eq_bot_iff] at hnd
        apply hnd
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro w _
        unfold LinearMap.BilinForm.IsOrtho
        have h := ha (w, w) (show (w : V) = w from rfl)
        unfold LinearMap.BilinForm.IsOrtho at h
        simp at h
        rw [map_sub, add_neg_eq_zero.mp h, sub_self]
      exact sub_eq_zero.mp hab
    · intro (ha : a = b) ⟨w₁, w₂⟩ (hw : w₁ = w₂)
      unfold LinearMap.BilinForm.IsOrtho
      simp [ha, hw]
  · exact orthogonalSum_nondegenerate B (-B) hnd (neg_nondegenerate B hnd)


/-- If the orthogonal direct sum `B₁ ⊕ B₂` is nondegenerate, then so is `B₁`. -/
lemma nondegenerate_fst_of_orthogonalSum
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (hnd : BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B₁ B₂)) :
    BilinForm.IsNondegenerate' B₁ := by
  rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff] at hnd ⊢
  intro v₁ hv₁
  have : (v₁, (0 : V₂)) = (0 : V₁ × V₂) := by
    apply hnd
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro ⟨w₁, w₂⟩ _
    unfold LinearMap.BilinForm.IsOrtho
    simp only [BilinForm.orthogonalSum_apply, map_zero, add_zero]
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv₁
    exact hv₁ w₁ Submodule.mem_top
  exact Prod.mk.inj this |>.1

/-- Given a totally isotropic subspace `W₁₂` for `B₁ ⊕ B₂` and a totally
isotropic subspace `W₂` for `B₂`, the projection of `W₁₂ ∩ (V₁ × W₂)` onto `V₁`
is a totally isotropic subspace for `B₁`. -/
theorem lagrangian_W1_isotropic
    {k : Type*} [Field k]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (W₁₂ : Submodule k (V₁ × V₂)) (W₂ : Submodule k V₂)
    (hW₁₂_iso : ∀ w₁ ∈ W₁₂, ∀ w₂ ∈ W₁₂, BilinForm.orthogonalSum B₁ B₂ w₁ w₂ = 0)
    (hW₂_iso : ∀ w₁ ∈ W₂, ∀ w₂ ∈ W₂, B₂ w₁ w₂ = 0) :
    let W₁ := Submodule.map (LinearMap.fst k V₁ V₂) (W₁₂ ⊓ Submodule.prod ⊤ W₂)
    W₁ ≤ LinearMap.BilinForm.orthogonal B₁ W₁ := by
  intro W₁ x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  unfold LinearMap.BilinForm.IsOrtho
  rw [Submodule.mem_map] at hx hy
  obtain ⟨⟨x₁, x₂⟩, hxm, rfl⟩ := hx
  obtain ⟨⟨y₁, y₂⟩, hym, rfl⟩ := hy
  simp only [LinearMap.fst_apply]
  simp only [Submodule.mem_inf, Submodule.mem_prod] at hxm hym
  have h1 := hW₁₂_iso (y₁, y₂) hym.1 (x₁, x₂) hxm.1
  simp only [BilinForm.orthogonalSum_apply] at h1
  have h2 := hW₂_iso y₂ hym.2.2 x₂ hxm.2.2
  rw [h2, add_zero] at h1
  exact h1


/-- Convert the orthogonal-complement formulation of nondegeneracy into Mathlib's
`BilinForm.Nondegenerate` predicate. -/
lemma IsNondegenerate'_to_Nondegenerate_inline
    {k₀ : Type*} [Field k₀]
    {V : Type*} [AddCommGroup V] [Module k₀ V] [FiniteDimensional k₀ V]
    {B : LinearMap.BilinForm k₀ V}
    (h : BilinForm.IsNondegenerate' B) : B.Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingRight
  intro y hy
  rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff] at h
  exact h y (by rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro n _; exact hy n)

/-- A Lagrangian subspace of a nondegenerate bilinear form has dimension equal
to half the dimension of the ambient space. -/
theorem lagrangian_finrank_inline
    {k₀ : Type*} [Field k₀]
    {V : Type*} [AddCommGroup V] [Module k₀ V] [FiniteDimensional k₀ V]
    (B : LinearMap.BilinForm k₀ V)
    (W : Submodule k₀ V)
    (hW_lagrangian : LinearMap.BilinForm.orthogonal B W = W)
    (hB_nd : BilinForm.IsNondegenerate' B) :
    2 * Module.finrank k₀ W = Module.finrank k₀ V := by
  have hB_nd' : B.Nondegenerate := IsNondegenerate'_to_Nondegenerate_inline hB_nd
  have h := LinearMap.BilinForm.finrank_orthogonal hB_nd' W
  rw [hW_lagrangian] at h
  omega

/-- Hard direction of the Lagrangian extraction lemma: with the same data as in
`lagrangian_W1_isotropic`, the projection `W₁` not only is contained in its
orthogonal complement (the easy direction), but actually equals it. This step
of the proof currently contains a `sorry`. -/
theorem lagrangian_extraction_hard_direction
    {k : Type*} [Field k]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (W₁₂ : Submodule k (V₁ × V₂)) (W₂ : Submodule k V₂)
    (hW₁₂_iso : ∀ w₁ ∈ W₁₂, ∀ w₂ ∈ W₁₂, BilinForm.orthogonalSum B₁ B₂ w₁ w₂ = 0)
    (hW₁₂_orth : LinearMap.BilinForm.orthogonal (BilinForm.orthogonalSum B₁ B₂) W₁₂ = W₁₂)
    (hW₁₂_nd : BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B₁ B₂))
    (hW₂_iso : ∀ w₁ ∈ W₂, ∀ w₂ ∈ W₂, B₂ w₁ w₂ = 0)
    (hW₂_orth : LinearMap.BilinForm.orthogonal B₂ W₂ = W₂)
    (hW₂_nd : BilinForm.IsNondegenerate' B₂) :
    let W₁ := Submodule.map (LinearMap.fst k V₁ V₂) (W₁₂ ⊓ Submodule.prod ⊤ W₂)
    LinearMap.BilinForm.orthogonal B₁ W₁ ≤ W₁ := by
  intro W₁


  have easy : W₁ ≤ LinearMap.BilinForm.orthogonal B₁ W₁ := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    unfold LinearMap.BilinForm.IsOrtho
    rw [Submodule.mem_map] at hx hy
    obtain ⟨⟨x₁, x₂⟩, hxm, rfl⟩ := hx
    obtain ⟨⟨y₁, y₂⟩, hym, rfl⟩ := hy
    simp only [LinearMap.fst_apply]
    simp only [Submodule.mem_inf, Submodule.mem_prod] at hxm hym
    have h1 := hW₁₂_iso (y₁, y₂) hym.1 (x₁, x₂) hxm.1
    simp only [BilinForm.orthogonalSum_apply] at h1
    have h2 := hW₂_iso y₂ hym.2.2 x₂ hxm.2.2
    rw [h2, add_zero] at h1
    exact h1


  have hB₁_nd : BilinForm.IsNondegenerate' B₁ := by
    rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff] at hW₁₂_nd ⊢
    intro v₁ hv₁
    have : (v₁, (0 : V₂)) = (0 : V₁ × V₂) := by
      apply hW₁₂_nd
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro ⟨w₁, w₂⟩ _
      unfold LinearMap.BilinForm.IsOrtho
      simp only [BilinForm.orthogonalSum_apply, map_zero, add_zero]
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv₁
      exact hv₁ w₁ Submodule.mem_top
    exact Prod.mk.inj this |>.1
  have hB₁_nd' : B₁.Nondegenerate := IsNondegenerate'_to_Nondegenerate_inline hB₁_nd


  have h_eq : W₁ = LinearMap.BilinForm.orthogonal B₁ W₁ := by
    apply Submodule.eq_of_le_of_finrank_le easy
    have h_orth_rank := LinearMap.BilinForm.finrank_orthogonal hB₁_nd' W₁


    sorry
  rw [← h_eq]

/-- Hyperbolic cancellation: if `B₁ ⊕ B₂` is hyperbolic and `B₂` is hyperbolic,
then `B₁` is hyperbolic. -/
lemma hyperbolic_cancel_summand
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (h_sum : BilinForm.IsHyperbolic (BilinForm.orthogonalSum B₁ B₂))
    (h₂ : BilinForm.IsHyperbolic B₂) :
    BilinForm.IsHyperbolic B₁ := by
  obtain ⟨W₁₂, hW₁₂_iso, hW₁₂_orth, hW₁₂_nd⟩ := h_sum
  obtain ⟨W₂, hW₂_iso, hW₂_orth, hW₂_nd⟩ := h₂

  refine ⟨Submodule.map (LinearMap.fst k V₁ V₂) (W₁₂ ⊓ Submodule.prod ⊤ W₂), ?_, ?_, ?_⟩
  ·

    intro v₁ hv₁ u₁ hu₁
    rw [Submodule.mem_map] at hv₁ hu₁
    obtain ⟨⟨v₁', v₂'⟩, hv, rfl⟩ := hv₁
    obtain ⟨⟨u₁', u₂'⟩, hu, rfl⟩ := hu₁
    simp only [Submodule.mem_inf, Submodule.mem_prod] at hv hu
    simp only [LinearMap.fst_apply]
    have h1 := hW₁₂_iso (v₁', v₂') hv.1 (u₁', u₂') hu.1
    simp only [BilinForm.orthogonalSum_apply] at h1
    have h2 := hW₂_iso v₂' hv.2.2 u₂' hu.2.2
    rw [h2, add_zero] at h1; exact h1
  ·
    ext v₁; constructor
    ·
      intro hv₁
      exact lagrangian_extraction_hard_direction B₁ B₂ W₁₂ W₂
        hW₁₂_iso hW₁₂_orth hW₁₂_nd hW₂_iso hW₂_orth hW₂_nd hv₁
    ·
      intro hv₁
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u₁ hu₁
      unfold LinearMap.BilinForm.IsOrtho
      rw [Submodule.mem_map] at hv₁ hu₁
      obtain ⟨⟨v₁', v₂'⟩, hv, rfl⟩ := hv₁
      obtain ⟨⟨u₁', u₂'⟩, hu, rfl⟩ := hu₁
      simp only [Submodule.mem_inf, Submodule.mem_prod] at hv hu
      simp only [LinearMap.fst_apply]
      have h1 := hW₁₂_iso (u₁', u₂') hu.1 (v₁', v₂') hv.1
      simp only [BilinForm.orthogonalSum_apply] at h1
      have h2 := hW₂_iso u₂' hu.2.2 v₂' hv.2.2
      rw [h2, add_zero] at h1
      exact h1
  ·
    exact nondegenerate_fst_of_orthogonalSum B₁ B₂ hW₁₂_nd

/-- Hyperbolicity is preserved under isometry: if `(V₁, B₁)` is isometric to a
hyperbolic formed space `(V₂, B₂)`, then `B₁` is hyperbolic. -/
theorem isHyperbolic_of_isometric
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (φ : V₁ ≃ₗ[k] V₂) (hiso : IsFormedSpaceIsometry B₁ B₂ φ)
    (hH : BilinForm.IsHyperbolic B₂) :
    BilinForm.IsHyperbolic B₁ := by
  obtain ⟨W₂, hW₂_iso, hW₂_orth, hnd₂⟩ := hH
  refine ⟨Submodule.comap φ.toLinearMap W₂, ?_, ?_, ?_⟩
  ·
    intro v₁ hv₁ v₂ hv₂
    rw [← hiso v₁ v₂]; exact hW₂_iso (φ v₁) hv₁ (φ v₂) hv₂
  ·
    ext v
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_comap,
               LinearEquiv.coe_toLinearMap]
    constructor
    · intro hv; rw [← hW₂_orth, LinearMap.BilinForm.mem_orthogonal_iff]
      intro w₂ hw₂; unfold LinearMap.BilinForm.IsOrtho
      obtain ⟨u, rfl⟩ := φ.surjective w₂; rw [hiso u v]; exact hv u hw₂
    · intro hv w hw; unfold LinearMap.BilinForm.IsOrtho; rw [← hiso w v]
      rw [← hW₂_orth] at hv; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
      exact hv (φ w) hw
  ·
    rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff]
    intro v hv
    have hφv : φ v = 0 := by
      rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff] at hnd₂; apply hnd₂
      rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro w _
      unfold LinearMap.BilinForm.IsOrtho; obtain ⟨u, rfl⟩ := φ.surjective w
      rw [hiso u v]; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
      exact hv u Submodule.mem_top
    exact φ.injective (by rw [hφv, map_zero])

/-- Combination of cancellation and isometry-preservation: if `X ⊕ H₁` is
isometric to a hyperbolic space `H₂` and `H₁` is hyperbolic, then `X` is
hyperbolic. -/
theorem isHyperbolic_of_orthogonalSum_hyperbolic_isometric
    {X H₁ H₂ : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup H₁] [Module k H₁] [FiniteDimensional k H₁]
    [AddCommGroup H₂] [Module k H₂]
    (B_X : LinearMap.BilinForm k X) (B_H₁ : LinearMap.BilinForm k H₁)
    (B_H₂ : LinearMap.BilinForm k H₂)
    (hH₁ : BilinForm.IsHyperbolic B_H₁)
    (hH₂ : BilinForm.IsHyperbolic B_H₂)
    (hiso : FormedSpacesIsometric (BilinForm.orthogonalSum B_X B_H₁) B_H₂) :
    BilinForm.IsHyperbolic B_X := by
  obtain ⟨φ, hφ⟩ := hiso
  exact hyperbolic_cancel_summand B_X B_H₁
    (isHyperbolic_of_isometric _ B_H₂ φ hφ hH₂) hH₁


variable {U X Y : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

/-- A rearrangement linear equivalence permuting the four factors of
`(X × Y) × (U × U)` into `(U × X) × (U × Y)`. -/
noncomputable def rearrangeEquiv : ((X × Y) × (U × U)) ≃ₗ[k] ((U × X) × (U × Y)) :=
  (show ((X × Y) × (U × U)) ≃ₗ[k] ((U × X) × (U × Y)) from
  { toFun := fun p => ((p.2.1, p.1.1), (p.2.2, p.1.2))
    invFun := fun p => ((p.1.2, p.2.2), (p.1.1, p.2.1))
    left_inv := by intro p; ext <;> rfl
    right_inv := by intro p; ext <;> rfl
    map_add' := by intro ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
    map_smul' := by intro _ ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl })


/-- Garrett's Chapter 7 hyperbolicity result: if `(U ⊕ X) ≃ (U ⊕ Y)` is an
isometry of nondegenerate formed spaces, then the orthogonal direct sum
`X ⊕ (-Y)` is hyperbolic. -/
theorem orthogonal_direct_sum_neg_isHyperbolic
    (B_U : LinearMap.BilinForm k U) (B_X : LinearMap.BilinForm k X)
    (B_Y : LinearMap.BilinForm k Y)
    (hU_nd : BilinForm.IsNondegenerate' B_U)
    (_hX_nd : BilinForm.IsNondegenerate' B_X)
    (hY_nd : BilinForm.IsNondegenerate' B_Y)
    (φ : (U × X) ≃ₗ[k] (U × Y))
    (hφ : IsFormedSpaceIsometry
      (BilinForm.orthogonalSum B_U B_X)
      (BilinForm.orthogonalSum B_U B_Y) φ) :
    BilinForm.IsHyperbolic (BilinForm.orthogonalSum B_X (-B_Y)) := by

  have hH : BilinForm.IsHyperbolic (BilinForm.orthogonalSum B_U (-B_U)) :=
    directSum_neg_isHyperbolic B_U hU_nd

  have hUY_nd : BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B_U B_Y) :=
    orthogonalSum_nondegenerate B_U B_Y hU_nd hY_nd

  have hform_eq : BilinForm.orthogonalSum (BilinForm.orthogonalSum B_U B_Y)
      (-(BilinForm.orthogonalSum B_U B_Y)) =
      BilinForm.orthogonalSum (BilinForm.orthogonalSum B_U B_Y)
        (BilinForm.orthogonalSum (-B_U) (-B_Y)) := by
    congr 1; exact neg_orthogonalSum_eq B_U B_Y
  have hTarget : BilinForm.IsHyperbolic (BilinForm.orthogonalSum
      (BilinForm.orthogonalSum B_U B_Y) (-(BilinForm.orthogonalSum B_U B_Y))) :=
    directSum_neg_isHyperbolic (BilinForm.orthogonalSum B_U B_Y) hUY_nd

  rw [hform_eq] at hTarget


  let Ψ := (rearrangeEquiv (k := k) (U := U) (X := X) (Y := Y)).trans
    (φ.prodCongr (LinearEquiv.refl k (U × Y)))

  have hΨ : IsFormedSpaceIsometry
      (BilinForm.orthogonalSum (BilinForm.orthogonalSum B_X (-B_Y))
        (BilinForm.orthogonalSum B_U (-B_U)))
      (BilinForm.orthogonalSum (BilinForm.orthogonalSum B_U B_Y)
        (BilinForm.orthogonalSum (-B_U) (-B_Y))) Ψ := by
    intro v w
    simp only [Ψ, LinearEquiv.trans_apply, BilinForm.orthogonalSum_apply,
               LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
               LinearMap.neg_apply, rearrangeEquiv]

    have h := hφ (v.2.1, v.1.1) (w.2.1, w.1.1)
    simp only [BilinForm.orthogonalSum_apply] at h
    linear_combination h

  exact isHyperbolic_of_orthogonalSum_hyperbolic_isometric
    (BilinForm.orthogonalSum B_X (-B_Y))
    (BilinForm.orthogonalSum B_U (-B_U))
    (BilinForm.orthogonalSum (BilinForm.orthogonalSum B_U B_Y)
      (BilinForm.orthogonalSum (-B_U) (-B_Y)))
    hH hTarget ⟨Ψ, hΨ⟩

end Garrett


namespace Formalization

/-- Formalization-namespace wrapper for `orthogonal_direct_sum_neg_isHyperbolic`,
exposing the Chapter 7 hyperbolicity result under the `Formalization` namespace. -/
theorem ch7_directSum_neg_hyperbolic
    {k : Type*} [Field k]
    {U X Y : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (B_U : LinearMap.BilinForm k U) (B_X : LinearMap.BilinForm k X)
    (B_Y : LinearMap.BilinForm k Y)
    (hU_nd : Garrett.BilinForm.IsNondegenerate' B_U)
    (hX_nd : Garrett.BilinForm.IsNondegenerate' B_X)
    (hY_nd : Garrett.BilinForm.IsNondegenerate' B_Y)
    (φ : (U × X) ≃ₗ[k] (U × Y))
    (hφ : Garrett.IsFormedSpaceIsometry
      (Garrett.BilinForm.orthogonalSum B_U B_X)
      (Garrett.BilinForm.orthogonalSum B_U B_Y) φ) :
    Garrett.BilinForm.IsHyperbolic (Garrett.BilinForm.orthogonalSum B_X (-B_Y)) :=
  Garrett.orthogonal_direct_sum_neg_isHyperbolic B_U B_X B_Y hU_nd hX_nd hY_nd φ hφ

end Formalization
