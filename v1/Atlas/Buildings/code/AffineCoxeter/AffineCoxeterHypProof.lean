/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusCorollary
import Atlas.Buildings.code.AffineCoxeter.FiniteProperParabolicsInstance
import Atlas.Buildings.code.AffineCoxeter.AffineCriterion

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone PerronFrobeniusProof

namespace AffineCoxeterHypProof

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- A Coxeter matrix is **crystallographic** if $2 \cos(\pi/m_{st}) \in \mathbb Z$ for all $s,t \in B$,
i.e. all entries of the doubled Gram matrix are integers. This is the condition for the associated
root system to admit an integral coroot lattice. -/
def IsCrystallographic (M : CoxeterMatrix B) : Prop :=
  ∀ s t : B, ∃ n : ℤ, 2 * CoxeterGroup.formVal M s t = ↑n

/-- For an indecomposable positive semidefinite Coxeter form $B$ (i.e. an affine type), the form
becomes positive definite (coercive) when restricted to vectors supported on any proper subset
$I \subsetneq B$ of simple reflections. This is the "spherical-on-parabolics" reduction. -/
theorem coercive_on_proper_subset_of_affine
    (M : CoxeterMatrix B)
    (hIndecomp : FormIndecomposable (fun s t => formVal M s t))
    (hPSD : ∀ v : B → ℝ, bilinForm M v v ≥ 0)
    (I : Finset B) (hI : I ≠ Finset.univ) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (v : B → ℝ), (∀ s, s ∉ I → v s = 0) →
        c * ∑ b : B, (v b) ^ 2 ≤ CoxeterGroup.bilinForm M v v := by sorry

/-- For a crystallographic Coxeter matrix, every positive root $\alpha \in \Phi^+$ has integer
coordinates in the simple-root basis: $\alpha = \sum_b n_b \alpha_b$ with $n_b \in \mathbb Z$. -/
theorem roots_integer_coords_of_crystallographic
    (M : CoxeterMatrix B)
    (hCrys : IsCrystallographic M) :
    ∀ α ∈ standardΦpos M, ∀ b : B, ∃ n : ℤ, α b = ↑n := by sorry

/-- Constructor: an affine Coxeter matrix that is additionally crystallographic satisfies the
hypotheses `AffineCoxeterHyp` (coercivity on proper parabolics + integral root coordinates)
needed for the rest of the affine theory. -/
noncomputable def AffineCoxeterHyp.mk' (M : CoxeterMatrix B)
    (hAff : IsAffineCoxeter M) (hCrys : IsCrystallographic M) :
    AffineCoxeterHyp M where
  coercive_on_proper_subset := by
    intro I hI
    unfold IsAffineCoxeter at hAff
    exact coercive_on_proper_subset_of_affine M hAff.1 hAff.2.1 I hI
  roots_integer_coords := roots_integer_coords_of_crystallographic M hCrys

end AffineCoxeterHypProof
