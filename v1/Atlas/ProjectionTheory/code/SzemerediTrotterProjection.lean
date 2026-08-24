/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.SzemerediTrotter

open Finset Real Set

namespace SzemerediTrotterProjection

/-- The orthogonal projection $\pi_\theta(p) = p_1 \cos\theta + p_2 \sin\theta$ of a
point $p \in \mathbb{R}^2$ in direction $\theta$, written in product form. -/
noncomputable def orthProj (θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * cos θ + p.2 * sin θ

/-- The image $\pi_\theta(X) \subset \mathbb{R}$ of a finite set $X \subset \mathbb{R}^2$
under the direction-$\theta$ projection. -/
noncomputable def projImage (θ : ℝ) (X : Finset (ℝ × ℝ)) : Finset ℝ :=
  X.image (orthProj θ)

/-- The set $D = D(X, S) \subset [0, \pi)$ of directions $\theta$ along which the
projection $\pi_\theta(X)$ has small image, $|\pi_\theta(X)| \le S$. -/
noncomputable def smallProjDirections (X : Finset (ℝ × ℝ)) (S : ℕ) : Set ℝ :=
  {θ : ℝ | θ ∈ Ico 0 π ∧ (projImage θ X).card ≤ S}

/-- Apply the Szemerédi--Trotter incidence theorem to the fiber-lines configuration:
for $X \subset \mathbb{R}^2$ and $n$ small-projection directions, the count
$n |X|$ is bounded by $|X| + nS + |X|^{2/3} (nS)^{2/3}$. -/
theorem st_fiber_incidence_bound
    (X : Finset (ℝ × ℝ)) (S : ℕ) (n : ℕ)
    (hn : n = (smallProjDirections X S).ncard)
    (hfin : (smallProjDirections X S).Finite)
    (hSlt : S < X.card) (hn2 : n ≥ 2) :
    (n : ℝ) * (X.card : ℝ) ≤
      (X.card : ℝ) + (n : ℝ) * (S : ℝ) +
        (X.card : ℝ) ^ ((2 : ℝ) / 3) * ((n : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3) := by
  classical

  let toFin2 : ℝ × ℝ → (Fin 2 → ℝ) := fun p => ![p.1, p.2]
  have toFin2_inj : Function.Injective toFin2 := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp only [toFin2] at h
    have h0 : (![a₁, b₁] : Fin 2 → ℝ) 0 = (![a₂, b₂] : Fin 2 → ℝ) 0 := congr_fun h 0
    have h1 : (![a₁, b₁] : Fin 2 → ℝ) 1 = (![a₂, b₂] : Fin 2 → ℝ) 1 := congr_fun h 1
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1

  let X' : Finset (Fin 2 → ℝ) := X.image toFin2
  have hX'card : X'.card = X.card := Finset.card_image_of_injective X toFin2_inj

  have hXne : X.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero (by omega))
  have hX'ne : X'.Nonempty := Finset.image_nonempty.mpr hXne

  let D : Finset ℝ := hfin.toFinset
  have hDcard : D.card = n := by
    rw [hn]
    exact (Set.ncard_eq_toFinset_card (smallProjDirections X S) hfin).symm

  have hDr : ∀ θ ∈ D, 0 ≤ θ ∧ θ < Real.pi := by
    intro θ hθ
    have hmem := hfin.mem_toFinset.mp hθ
    exact hmem.1

  have proj_eq : ∀ θ (p : ℝ × ℝ), ProjectionTheory.projR2 θ (toFin2 p) = orthProj θ p := by
    intro θ ⟨a, b⟩
    simp [ProjectionTheory.projR2, toFin2, orthProj, Matrix.cons_val_zero,
      Matrix.cons_val_one]

  have projImg_eq : ∀ θ, ProjectionTheory.projImageR2 θ X' = projImage θ X := by
    intro θ
    simp only [ProjectionTheory.projImageR2, projImage, X']
    rw [Finset.image_image]
    exact Finset.image_congr (fun p _ => proj_eq θ p)

  have hSb : ∀ θ ∈ D, (ProjectionTheory.projImageR2 θ X').card ≤ S := by
    intro θ hθ
    rw [projImg_eq]
    have hmem := hfin.mem_toFinset.mp hθ
    exact hmem.2

  obtain ⟨L, hLcard, hIncid⟩ := ProjectionTheory.fiber_lines_st_bound X' S D hDr hSb hX'ne

  have hST := SzemerediTrotter.szemeredi_trotter X' L

  have hIncid_r : (X.card : ℝ) * (n : ℝ) ≤ (SzemerediTrotter.incidenceCount X' L : ℝ) := by
    have h1 : X'.card * D.card ≤ SzemerediTrotter.incidenceCount X' L := hIncid
    rw [hX'card, hDcard] at h1
    exact_mod_cast h1
  rw [hX'card] at hST
  have hLcard_r : (L.card : ℝ) ≤ (n : ℝ) * (S : ℝ) := by
    have h1 : L.card ≤ S * D.card := hLcard
    rw [hDcard] at h1
    have h2 : L.card ≤ n * S := Nat.mul_comm S n ▸ h1
    exact_mod_cast h2


  calc (n : ℝ) * (X.card : ℝ)
      = (X.card : ℝ) * (n : ℝ) := by ring
    _ ≤ (SzemerediTrotter.incidenceCount X' L : ℝ) := hIncid_r
    _ ≤ (X.card : ℝ) + (L.card : ℝ) +
        (X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) := hST
    _ ≤ (X.card : ℝ) + (n : ℝ) * (S : ℝ) +
        (X.card : ℝ) ^ ((2 : ℝ) / 3) * ((n : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3) := by
      gcongr

/-- Algebraic lemma extracting the projection bound $n \le S^2/P + 1$ from the
Szemerédi--Trotter incidence inequality $nP \le P + nS + P^{2/3}(nS)^{2/3}$. -/
theorem st_algebraic_bound (n P S : ℕ) (hP : (P : ℝ) > 0) (hSP : S < P) (hn2 : n ≥ 2)
    (hST : (n : ℝ) * (P : ℝ) ≤ (P : ℝ) + (n : ℝ) * (S : ℝ) +
      (P : ℝ) ^ ((2:ℝ)/3) * ((n : ℝ) * (S : ℝ)) ^ ((2:ℝ)/3)) :
    (n : ℝ) ≤ (S : ℝ) ^ 2 / (P : ℝ) + 1 := by sorry

/-- **Szemerédi--Trotter projection theorem (finite case).** Under the assumption that
the set of small-projection directions is finite and $S < |X|$, we have
$|D(X, S)| \le S^2/|X| + 1$. -/
theorem szemeredi_trotter_projection_finite
    (X : Finset (ℝ × ℝ)) (S : ℕ)
    (hfin : (smallProjDirections X S).Finite) (hSlt : S < X.card) :
    ((smallProjDirections X S).ncard : ℝ) ≤ (S : ℝ) ^ 2 / (X.card : ℝ) + 1 := by
  classical
  set n := (smallProjDirections X S).ncard
  set P := X.card
  have hP_pos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  by_cases hn1 : n ≤ 1
  · calc (n : ℝ) ≤ 1 := by exact_mod_cast hn1
      _ ≤ (S : ℝ) ^ 2 / (P : ℝ) + 1 :=
          le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (Nat.cast_nonneg' P))
  · have hn2 : n ≥ 2 := by omega
    have hST := st_fiber_incidence_bound X S n rfl hfin hSlt hn2
    exact st_algebraic_bound n P S hP_pos hSlt hn2 hST

/-- **Szemerédi--Trotter projection theorem.** Let $X$ be a finite set of points in
$\mathbb{R}^2$ and $D = D(X, S)$ the set of directions $\theta \in [0, \pi)$ with
$|\pi_\theta(X)| \le S$. Then $|D| \le S^2/|X| + 1$ (with the convention that the bound
is vacuously satisfied when $D$ is infinite, since then $S \ge |X|$). -/
theorem szemeredi_trotter_projection (X : Finset (ℝ × ℝ)) (S : ℕ) :
    ((smallProjDirections X S).ncard : ℝ) ≤ (S : ℝ) ^ 2 / (X.card : ℝ) + 1 := by
  rcases (smallProjDirections X S).finite_or_infinite with hfin | hinf
  ·

    have hSlt : S < X.card := by
      by_contra h
      push Not at h
      exact (Set.Ico_infinite (show (0 : ℝ) < π from pi_pos)).not_finite
        (hfin.subset (fun θ hθ => ⟨hθ, (Finset.card_image_le).trans h⟩))
    exact szemeredi_trotter_projection_finite X S hfin hSlt
  ·
    simp only [hinf.ncard, Nat.cast_zero]
    exact add_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg' X.card)) one_pos.le

end SzemerediTrotterProjection

namespace SzemerediTrotter
open Classical

/-- **Beck's theorem / Szemerédi--Trotter lower bound on lines.** There exists a constant
$C > 0$ such that for any finite point set $E \subset \mathbb{R}^2$ and any choice of
$S$ lines through each point $x \in E$, the union
$L = \bigcup_{x \in E} L_x$ has size
$|L| \gtrsim \min(|E| \cdot S, |E|^{1/2} S^{3/2})$. -/
theorem szemeredi_trotter_lines_lower_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ (E : Finset (Fin 2 → ℝ)) (S : ℕ) (_ : 1 < S)
        (L_x : E → Finset Line2)
        (_ : ∀ x : E, (L_x x).card = S)
        (_ : ∀ x : E, ∀ ℓ ∈ L_x x, (x : Fin 2 → ℝ) ∈ ℓ),
        ((Finset.biUnion Finset.univ L_x).card : ℝ) ≥
          C * min ((E.card : ℝ) * S) ((E.card : ℝ) ^ ((1 : ℝ) / 2) * (S : ℝ) ^ ((3 : ℝ) / 2)) := by sorry

end SzemerediTrotter
