/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option maxHeartbeats 400000

open Set

namespace SphereArrangement

/-- Three-dimensional Euclidean space $\mathbb{R}^3$ used for the sphere-cutting bound. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- A sphere in $\mathbb{R}^3$ specified by a center and a strictly positive radius. -/
structure Sphere3 where
  center : R3
  radius : ℝ
  radius_pos : 0 < radius

/-- The underlying point set of a sphere: $\{x \in \mathbb{R}^3 : \|x - c\| = r\}$. -/
def Sphere3.toSet (S : Sphere3) : Set R3 :=
  Metric.sphere S.center S.radius

/-- The union $\bigcup_i S_i$ of a finite family of spheres in $\mathbb{R}^3$. -/
def sphereUnion (spheres : Fin n → Sphere3) : Set R3 :=
  ⋃ i, (spheres i).toSet

/-- Number of connected components of the complement of $\bigcup_i S_i$ in $\mathbb{R}^3$. -/
noncomputable def numComponentsComplement (spheres : Fin n → Sphere3) : ℕ :=
  Nat.card (ConnectedComponents (↥(sphereUnion spheres)ᶜ))

/-- A single sphere divides $\mathbb{R}^3$ into exactly $2$ connected components (interior and exterior). -/
theorem one_sphere_components
  (S : Fin 1 → Sphere3) : numComponentsComplement S = 2 := by sorry

/-- Inductive step: adding one more sphere to an arrangement of $m \ge 1$ spheres can increase the number of complementary components by at most $m(m-1) + 2$. -/
theorem sphere_addition_components
  {m : ℕ} (spheres : Fin (m + 1) → Sphere3) (hm : 1 ≤ m) :
  (numComponentsComplement spheres : ℤ) ≤
    (numComponentsComplement (fun i => spheres (Fin.castSucc i)) : ℤ) +
      ((m : ℤ) * ((m : ℤ) - 1) + 2) := by sorry

/-- Lemma 6.2.14: any arrangement of $n \ge 2$ spheres in $\mathbb{R}^3$ cuts the space into at most $n^3$ connected components. -/
theorem sphere_arrangement_components_le_cube {n : ℕ} (hn : 2 ≤ n) (spheres : Fin n → Sphere3) :
    numComponentsComplement spheres ≤ n ^ 3 := by
  suffices h : (numComponentsComplement spheres : ℤ) ≤ (n : ℤ) ^ 3 by exact_mod_cast h
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>

        have hadd := sphere_addition_components spheres (by omega : 1 ≤ 1)
        have hone := one_sphere_components (fun i => spheres (Fin.castSucc i))
        push_cast at hadd hone ⊢
        linarith
      | succ j =>

        have hadd := sphere_addition_components spheres (by omega : 1 ≤ j + 2)
        have ih' := ih (by omega : 2 ≤ j + 2) (fun i => spheres (Fin.castSucc i))
        push_cast at hadd ih' ⊢
        nlinarith

end SphereArrangement
