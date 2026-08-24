/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

set_option autoImplicit false
open scoped Manifold


/-- Algebraic data of the intersection form of a closed oriented $4$-manifold:
second Betti number $b_2 = b_2^+ + b_2^-$, signature $\sigma = b_2^+ - b_2^-$, parity, and a
symmetric bilinear form on $H^2(M; \mathbb{Z}) \cong \mathbb{Z}^{b_2}$. -/
structure Mfd4IntersectionForm where
  b₂ : ℕ
  b₂_plus : ℕ
  b₂_minus : ℕ
  rank_decomp : b₂ = b₂_plus + b₂_minus
  signature : ℤ
  signature_eq : signature = (b₂_plus : ℤ) - (b₂_minus : ℤ)
  isEven : Bool
  bilinForm : (Fin b₂ → ℤ) → (Fin b₂ → ℤ) → ℤ
  bilinForm_symm : ∀ x y, bilinForm x y = bilinForm y x

/-- An almost-complex structure $J$ on a smooth $4$-manifold (placeholder, witnessing existence). -/
structure Mfd4AlmostComplexStr (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] where
  mk' ::

/-- Topological data attached to a closed smooth $4$-manifold $M$: its intersection form `Q`
and Euler characteristic $\chi(M) = 2 + b_2(M)$ (for simply connected $M$). -/
class Mfd4Topology (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  Q : Mfd4IntersectionForm
  euler : ℤ
  euler_eq : euler = 2 + (Q.b₂ : ℤ)


/-- Chern and Pontrjagin number data for a closed $4$-manifold equipped with an almost complex
structure: $c_1^2 \cdot [M]$, $c_2 \cdot [M]$, with $c_2 = \chi(M)$. -/
structure HasChernPontrjaginData (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M] where
  c₁_sq : ℤ
  c₂ : ℤ
  c₂_eq_euler : c₂ = htop.euler

/-- First Pontrjagin number $p_1 \cdot [M] = c_1^2 - 2 c_2$, the Whitney sum relation for an
almost complex $4$-manifold. -/
def HasChernPontrjaginData.p₁ {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) : ℤ :=
  hcp.c₁_sq - 2 * hcp.c₂

/-- The rearranged Chern–Pontrjagin relation: $c_1^2 = 2 c_2 + p_1$. -/
theorem HasChernPontrjaginData.chern_pontrjagin_rel {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) :
    hcp.c₁_sq = 2 * hcp.c₂ + hcp.p₁ := by

  unfold HasChernPontrjaginData.p₁
  ring


/-- Data of a closed oriented $4$-manifold: Pontrjagin number $p_1$, Betti numbers
$b_2^\pm$, signature $\sigma$, and a symmetric intersection form on $H^2 \cong \mathbb{Z}^{b_2}$. -/
structure ClosedOriented4ManifoldData (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  p₁ : ℤ
  b₂_plus : ℕ
  b₂_minus : ℕ
  signature : ℤ
  signature_eq : signature = (b₂_plus : ℤ) - (b₂_minus : ℤ)
  intersectionForm : (Fin (b₂_plus + b₂_minus) → ℤ) →
    (Fin (b₂_plus + b₂_minus) → ℤ) → ℤ
  intersectionForm_symm : ∀ x y, intersectionForm x y = intersectionForm y x

/-- Hirzebruch signature theorem (axiomatized): $p_1 \cdot [M] = 3 \sigma(M)$ for closed
oriented $4$-manifolds. -/
theorem hirzebruch_signature_axiom
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (mfd : ClosedOriented4ManifoldData M) :
    mfd.p₁ = 3 * mfd.signature := by sorry

/-- Hirzebruch signature theorem (Theorem 1 of the chapter): $p_1(TM) \cdot [M] = 3 \sigma(M)$. -/
theorem hirzebruch_signature_theorem
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (mfd : ClosedOriented4ManifoldData M) :
    mfd.p₁ = 3 * mfd.signature :=
  hirzebruch_signature_axiom mfd

/-- Build closed-oriented manifold data from Chern–Pontrjagin data plus topological data. -/
def ClosedOriented4ManifoldData.ofChernPontrjagin
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) :
    ClosedOriented4ManifoldData M where
  p₁ := hcp.p₁
  b₂_plus := htop.Q.b₂_plus
  b₂_minus := htop.Q.b₂_minus
  signature := htop.Q.signature
  signature_eq := htop.Q.signature_eq
  intersectionForm := fun x y =>
    htop.Q.bilinForm
      (fun i => x (Fin.cast htop.Q.rank_decomp i))
      (fun i => y (Fin.cast htop.Q.rank_decomp i))
  intersectionForm_symm := fun _ _ => htop.Q.bilinForm_symm _ _


/-- Bundled data for a closed oriented almost-complex $4$-manifold: the underlying topology,
Euler number $\chi$, $c_1^2$, $c_2 = \chi$, and the Whitney relation $p_1 = c_1^2 - 2c_2$. -/
structure ChernPontrjaginDataClosed (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  mfd : ClosedOriented4ManifoldData M
  euler : ℤ
  c₁_sq : ℤ
  c₂ : ℤ
  c₂_eq_euler : c₂ = euler
  p₁_whitney : mfd.p₁ = c₁_sq - 2 * c₂

/-- The Chern–Pontrjagin relation $c_1^2 = 2 c_2 + p_1$ for closed almost complex $4$-manifolds. -/
theorem ChernPontrjaginDataClosed.chern_pontrjagin_rel
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (data : ChernPontrjaginDataClosed M) :
    data.c₁_sq = 2 * data.c₂ + data.mfd.p₁ := by
  linarith [data.p₁_whitney]

/-- Construct the bundled closed Chern–Pontrjagin data from `HasChernPontrjaginData` together
with `Mfd4Topology`, assuming the simply-connected case. -/
def ChernPontrjaginDataClosed.ofSimplyConnected
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) :
    ChernPontrjaginDataClosed M where
  mfd := ClosedOriented4ManifoldData.ofChernPontrjagin hcp
  euler := htop.euler
  c₁_sq := hcp.c₁_sq
  c₂ := hcp.c₂
  c₂_eq_euler := hcp.c₂_eq_euler
  p₁_whitney := by

    show (ClosedOriented4ManifoldData.ofChernPontrjagin hcp).p₁ = hcp.c₁_sq - 2 * hcp.c₂
    dsimp only [ClosedOriented4ManifoldData.ofChernPontrjagin, HasChernPontrjaginData.p₁]


/-- Corollary 1 (closed form): $c_1^2 \cdot [M] = 2 \chi(M) + 3 \sigma(M)$, obtained by combining
the Chern–Pontrjagin relation with the Hirzebruch signature theorem. -/
theorem chern_number_formula_closed
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (data : ChernPontrjaginDataClosed M) :
    data.c₁_sq = 2 * data.euler + 3 * data.mfd.signature := by

  have h_cp := data.chern_pontrjagin_rel

  have h_c2 := data.c₂_eq_euler

  have h_sig := hirzebruch_signature_theorem data.mfd

  linarith

/-- Corollary 1: for a closed almost complex $4$-manifold,
$c_1^2 \cdot [M] = 2 \chi(M) + 3 \sigma(M)$. -/
theorem chern_number_formula
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) :
    hcp.c₁_sq = 2 * htop.euler + 3 * htop.Q.signature :=
  chern_number_formula_closed (ChernPontrjaginDataClosed.ofSimplyConnected hcp)


/-- Generic algebraic data needed to state the almost-complex existence criterion: rank of
$H^2$, Euler number $\chi$, signature $\sigma$, and a symmetric bilinear pairing modeling the
intersection form $Q$. -/
structure AlmostComplexObstructionDataGeneral (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  rank_H2 : ℕ
  euler : ℤ
  signature : ℤ
  pairing : (Fin rank_H2 → ℤ) → (Fin rank_H2 → ℤ) → ℤ
  pairing_symm : ∀ (α β : Fin rank_H2 → ℤ), pairing α β = pairing β α

/-- The square $\alpha^2 \cdot [M] = Q(\alpha, \alpha)$ evaluated via the bilinear pairing. -/
def AlmostComplexObstructionDataGeneral.square_eval
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (obsData : AlmostComplexObstructionDataGeneral M)
    (α : Fin obsData.rank_H2 → ℤ) : ℤ :=
  obsData.pairing α α

/-- Self-pairing $Q([A], [A])$ of a homology class with itself under the intersection form. -/
def AlmostComplexObstructionDataGeneral.Q_selfpairing
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (obsData : AlmostComplexObstructionDataGeneral M)
    (A : Fin obsData.rank_H2 → ℤ) : ℤ :=
  obsData.pairing A A

/-- Witness that an almost complex structure `J` has first Chern class with prescribed coordinates
in the basis of $H^2(M; \mathbb{Z})$. -/
structure HasFirstChernClassGeneral
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (J : Mfd4AlmostComplexStr M)
    (obsData : AlmostComplexObstructionDataGeneral M) where
  c₁_coords : Fin obsData.rank_H2 → ℤ


/-- Theorem 2 (almost-complex existence): there exists an almost complex structure $J$ on $M^4$
with $\alpha = c_1(TM, J)$ iff $\alpha^2 \cdot [M] = 2\chi + 3\sigma$ and
$\alpha \cdot [A] \equiv Q([A], [A]) \pmod 2$ for every $[A] \in H_2(M; \mathbb{Z})$. -/
theorem almost_complex_structure_criterion
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (obsData : AlmostComplexObstructionDataGeneral M)
    (α : Fin obsData.rank_H2 → ℤ) :
    (∃ (J : Mfd4AlmostComplexStr M)
       (hc : HasFirstChernClassGeneral J obsData),
      hc.c₁_coords = α) ↔
    (obsData.square_eval α = 2 * obsData.euler + 3 * obsData.signature ∧
     ∀ (A : Fin obsData.rank_H2 → ℤ),
       obsData.pairing α A % 2 = obsData.Q_selfpairing A % 2) := by sorry


/-- Obstruction data for an almost-complex structure, tied to the ambient `Mfd4Topology`: the
rank of $H^2$ matches $b_2(M)$, and a symmetric pairing models the intersection form. -/
structure AlmostComplexObstructionData (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M] where
  rank_H2 : ℕ
  rank_eq : rank_H2 = htop.Q.b₂
  pairing : (Fin rank_H2 → ℤ) → (Fin rank_H2 → ℤ) → ℤ
  pairing_symm : ∀ (α β : Fin rank_H2 → ℤ), pairing α β = pairing β α

/-- Forget the link to `Mfd4Topology` and produce general almost-complex obstruction data. -/
def AlmostComplexObstructionData.toGeneral
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (obsData : AlmostComplexObstructionData M) :
    AlmostComplexObstructionDataGeneral M where
  rank_H2 := obsData.rank_H2
  euler := htop.euler
  signature := htop.Q.signature
  pairing := obsData.pairing
  pairing_symm := obsData.pairing_symm

/-- Witness that an almost complex structure `J` has a first Chern class with the given
integer coordinates in the obstruction basis. -/
structure HasFirstChernClass
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (J : Mfd4AlmostComplexStr M)
    (obsData : AlmostComplexObstructionData M) where
  c₁_coords : Fin obsData.rank_H2 → ℤ


/-- Number-theoretic lemma: $14$ is not a sum of two integer squares, used in the obstruction
argument for $\mathbb{CP}^2 \# \mathbb{CP}^2$. -/
theorem not_sum_of_two_squares_14 : ∀ a b : ℤ, a ^ 2 + b ^ 2 ≠ 14 := by
  intro a b h

  have ha2 : a ^ 2 ≤ 14 := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ 14 := by nlinarith [sq_nonneg a]
  have ha_lo : -4 < a := by nlinarith [sq_nonneg (a + 4)]
  have ha_hi : a < 4 := by nlinarith [sq_nonneg (a - 4)]
  have hb_lo : -4 < b := by nlinarith [sq_nonneg (b + 4)]
  have hb_hi : b < 4 := by nlinarith [sq_nonneg (b - 4)]

  interval_cases a <;> interval_cases b <;> omega

/-- Obstruction example: $\mathbb{CP}^2 \# \mathbb{CP}^2$ (with $b_2 = 2$, $\sigma = 2$,
$\chi = 4$) admits no almost-complex structure, since the Chern number formula forces
$c_1^2 = 14$, which cannot be written as a sum of two squares. -/
theorem CP2_CP2_no_acs_full
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]

    (_hb₂ : htop.Q.b₂ = 2)

    (hσ : htop.Q.signature = 2)

    (hχ : htop.euler = 4)

    (hcp : HasChernPontrjaginData M)

    (a b : ℤ)
    (hc₁_decomp : hcp.c₁_sq = a ^ 2 + b ^ 2) :
    False := by

  have h_formula := chern_number_formula hcp

  have h14 : a ^ 2 + b ^ 2 = 14 := by linarith

  exact not_sum_of_two_squares_14 a b h14
