/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsAlgClosed.Basic

section BertiniPredicates

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [Module k V]

/-- Opaque predicate asserting that a subset of `ℙ(V)` is a smooth (closed) subvariety. -/
opaque IsSmoothSubvariety : Set (Projectivization k V) → Prop

/-- The hyperplane in `ℙ(V)` cut out by a point `H ∈ ℙ(V*)`, namely the zero locus of a
representative linear form. -/
noncomputable def projectiveHyperplane :
    Projectivization k (Module.Dual k V) → Set (Projectivization k V) :=
  fun H => {p : Projectivization k V | (Projectivization.rep H) (Projectivization.rep p) = 0}

/-- Opaque predicate asserting that a subset of the dual projective space `ℙ(V*)`
is a nonempty Zariski-open subset. -/
opaque IsNonemptyZariskiOpen :
  Set (Projectivization k (Module.Dual k V)) → Prop

/-- Opaque predicate asserting that a subset of the dual projective space `ℙ(V*)`
is a proper Zariski-closed subset (i.e., closed and not the whole space). -/
opaque IsProperZariskiClosed :
  Set (Projectivization k (Module.Dual k V)) → Prop

end BertiniPredicates

/-- Bertini "bad locus" lemma: For a smooth projective subvariety `X`, the set of
hyperplanes `H` for which `X ∩ H` is not smooth is contained in a proper closed subset
of the dual projective space. -/
theorem bertini_bad_locus_in_proper_closed
    (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (X : Set (Projectivization k V))
    (hX : IsSmoothSubvariety k V X) :
    ∃ W : Set (Projectivization k (Module.Dual k V)),
      IsProperZariskiClosed k V W ∧
      {H : Projectivization k (Module.Dual k V) |
        ¬ IsSmoothSubvariety k V (X ∩ projectiveHyperplane k V H)} ⊆ W := by sorry

/-- The complement of a proper Zariski-closed subset of `ℙ(V*)` is a nonempty Zariski open. -/
theorem proper_closed_complement_nonempty_open
    (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Set (Projectivization k (Module.Dual k V)))
    (hW : IsProperZariskiClosed k V W) :
    IsNonemptyZariskiOpen k V Wᶜ := by sorry

/-- Bertini for proper hyperplane sections (Theorem 22.1): For a smooth projective
subvariety `X ⊆ ℙ(V)`, there is a nonempty Zariski-open set of hyperplanes `H ∈ ℙ(V*)`
such that `X ∩ H` is smooth. -/
theorem bertini_generic_hyperplane_smooth_proper
    (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (X : Set (Projectivization k V))
    (hX : IsSmoothSubvariety k V X) :
    ∃ U : Set (Projectivization k (Module.Dual k V)),
      IsNonemptyZariskiOpen k V U ∧
      ∀ H ∈ U, IsSmoothSubvariety k V (X ∩ projectiveHyperplane k V H) := by


  obtain ⟨W, hW_closed, hB_sub_W⟩ := bertini_bad_locus_in_proper_closed k V X hX


  have hWc_open : IsNonemptyZariskiOpen k V Wᶜ :=
    proper_closed_complement_nonempty_open k V W hW_closed


  exact ⟨Wᶜ, hWc_open, fun H hH => by_contra (fun hBad => hH (hB_sub_W hBad))⟩
