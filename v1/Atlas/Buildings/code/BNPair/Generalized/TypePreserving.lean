/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Generalized.Defs

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

namespace GeneralizedBNPair

variable {B_idx : Type*} [Fintype B_idx] [DecidableEq B_idx]
variable {Gt : Type*} [Group Gt] {M : CoxeterMatrix B_idx}
variable (gbp : GeneralizedBNPair Gt M)

/-- The enlarged torus is contained in the enlarged Borel: $\tilde T = \tilde B \cap \tilde N
\leq \tilde B$. -/
theorem Tt_le_Bt : gbp.Tt ≤ gbp.Bt := by
  rw [gbp.Tt_eq]
  exact inf_le_left

/-- **Decomposition of $\tilde B$.** Every $x \in \tilde B$ factors as $x = t \cdot g$
with $t \in \tilde T$ and $g \in G \cap \tilde B$. Specializes the $\tilde G$-decomposition
to $\tilde B$. -/
theorem Bt_decomp_from_Gt :
    ∀ (x : Gt) (_ : x ∈ gbp.Bt),
      ∃ (t : Gt) (_ : t ∈ gbp.Tt) (g : Gt) (_ : g ∈ gbp.G) (_ : g ∈ gbp.Bt),
        x = t * g := by
  intro x hx
  obtain ⟨t, ht, g, hg, hdecomp⟩ := gbp.Gt_decomp x
  refine ⟨t, ht, g, hg, ?_, hdecomp⟩
  have hg_eq : g = t⁻¹ * x := by
    have : t * g = x := hdecomp.symm
    rw [← this, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hg_eq]
  exact gbp.Bt.mul_mem (gbp.Bt.inv_mem (gbp.Tt_le_Bt ht)) hx

/-- An element $t \in \tilde G$ acts trivially on types of the standard apartment:
for every simple reflection $s$ and every $N$-lift $n$ of $s$, the conjugate
$t n t^{-1}$ is again an $N$-lift of the *same* simple reflection $s$. -/
def ActsTriviallyOnTypes (t : Gt) : Prop :=
  ∀ (s : B_idx) (n : gbp.strictBNPair.N),
    gbp.strictBNPair.π n = M.toCoxeterSystem.simple s →
    ∃ (n' : gbp.strictBNPair.N),
      gbp.strictBNPair.π n' = M.toCoxeterSystem.simple s ∧
      ((n' : gbp.G) : Gt) = t * ((n : gbp.G) : Gt) * t⁻¹

/-- $g \in \tilde G$ preserves types on the base chamber: synonym for
`ActsTriviallyOnTypes g`, packaged to clarify the geometric meaning. -/
def PreservesTypesOnBaseChbr (g : Gt) : Prop :=
  gbp.ActsTriviallyOnTypes g

/-- $g \in \tilde G$ preserves types on the chamber $h \cdot C_0$: this means the
conjugate $h^{-1} g h$ preserves types on the base chamber $C_0$. -/
def PreservesTypesOnChamber (g h : Gt) : Prop :=
  gbp.PreservesTypesOnBaseChbr (h⁻¹ * g * h)

/-- **Type-preservation is a global property.** If $g \in \tilde G$ preserves types on
*any* single chamber $h \cdot C_0$, then $g \in G$ (the type-preserving subgroup).
The converse "everything in $G$ preserves types everywhere" is built into the
generalized BN-pair definition; this theorem is the rigidity half: local
type-preservation already forces global membership. -/
theorem TypePreservingImpliesGlobal
    (g : Gt) (h : Gt) (hpres : gbp.PreservesTypesOnChamber g h) :
    g ∈ gbp.G := by


  obtain ⟨h', hh'G, hh'stab, hh'types⟩ :=
    gbp.strong_transitivity_for_types (h⁻¹ * g * h) hpres

  have hprod_in_G : h' * (h⁻¹ * g * h) ∈ gbp.G :=
    gbp.building_uniqueness_lemma _ hh'stab hh'types

  have hconj_in_G : h⁻¹ * g * h ∈ gbp.G := by
    have : h⁻¹ * g * h = h'⁻¹ * (h' * (h⁻¹ * g * h)) := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact gbp.G.mul_mem (gbp.G.inv_mem hh'G) hprod_in_G

  have hg_eq : g = h * (h⁻¹ * g * h) * h⁻¹ := by
    simp [mul_assoc, mul_inv_cancel]
  rw [hg_eq]
  exact gbp.G_normal.conj_mem _ hconj_in_G h

/-- Alias for `TypePreservingImpliesGlobal` emphasizing the "local-to-global" flavor:
preserving types at one chamber implies $g$ belongs to the type-preserving subgroup $G$. -/
theorem LocalTypePreservingImpliesGlobal
    (g : Gt) (h : Gt) (hpres : gbp.PreservesTypesOnChamber g h) :
    g ∈ gbp.G :=
  gbp.TypePreservingImpliesGlobal g h hpres

end GeneralizedBNPair
