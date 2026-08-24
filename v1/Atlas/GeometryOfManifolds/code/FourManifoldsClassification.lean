/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.FourManifoldsSW

set_option autoImplicit false


/-- Rokhlin's theorem: the signature $\sigma(M)$ of a closed simply connected smooth $4$-manifold
with even intersection form is divisible by $16$. -/
theorem rokhlin_signature
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [_hsc : IsCompactSimplyConnected4Manifold M]
    [htop : Has4ManifoldTopology M]
    (heven : htop.Q.isEven = true) :
    (16 : ℤ) ∣ htop.Q.signature := by sorry


/-- Donaldson's diagonalizability theorem (positive definite case): if the intersection form $Q$
of a closed simply connected smooth $4$-manifold is positive definite, then $Q$ is diagonalizable
over $\mathbb{Z}$ (i.e. equivalent to the standard form $\mathrm{diag}(1,\ldots,1)$). -/
theorem donaldson_definite_diagonalizable
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [_hsc : IsCompactSimplyConnected4Manifold M]
    [htop : Has4ManifoldTopology M]
    (hdef : htop.Q.IsPositiveDefinite) :
    htop.Q.IsDiagonal := by sorry

/-- Donaldson's diagonalizability theorem (negative definite case): a negative definite
intersection form on a closed simply connected smooth $4$-manifold is diagonalizable
over $\mathbb{Z}$ (equivalent to $\mathrm{diag}(-1,\ldots,-1)$). -/
theorem donaldson_negdef_diagonalizable
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [_hsc : IsCompactSimplyConnected4Manifold M]
    [htop : Has4ManifoldTopology M]
    (hdef : htop.Q.IsNegativeDefinite) :
    htop.Q.IsDiagonal := by sorry


/-- Freedman's classification: two closed simply connected topological $4$-manifolds with the
same $b_2$, signature $\sigma$, and parity of the intersection form are homeomorphic. -/
theorem freedman_homeomorphic_of_same_invariants
    {M₁ M₂ : Type*}
    [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M₁]
    [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M₂]
    [_hsc₁ : IsCompactSimplyConnected4Manifold M₁]
    [_hsc₂ : IsCompactSimplyConnected4Manifold M₂]
    [htop₁ : Has4ManifoldTopology M₁] [htop₂ : Has4ManifoldTopology M₂]
    (hb₂ : htop₁.Q.b₂ = htop₂.Q.b₂)
    (hσ : htop₁.Q.signature = htop₂.Q.signature)
    (hparity : htop₁.Q.isEven = htop₂.Q.isEven) :
    AreHomeomorphic4Manifolds M₁ M₂ := by sorry
