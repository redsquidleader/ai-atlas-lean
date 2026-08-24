/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.IsogenyVolcano
import Atlas.EllipticCurves.code.Supersingular
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Polynomial Finset

namespace SupersingularIsogenyGraph

/-- The type of supersingular `j`-invariants over the algebraic closure of `𝔽_p`.
These are the `j`-invariants of supersingular elliptic curves in characteristic `p`,
all of which lie in `𝔽_{p^2}` (Theorem 13.16). -/
noncomputable def SupersingularJInvariants (p : ℕ) [Fact (Nat.Prime p)] : Type := by sorry

/-- The set of supersingular `j`-invariants in characteristic `p` is finite. -/
noncomputable instance SupersingularJInvariants.instFintype (p : ℕ) [Fact (Nat.Prime p)] :
  Fintype (SupersingularJInvariants p) := by sorry

/-- Equality of supersingular `j`-invariants is decidable. -/
noncomputable instance SupersingularJInvariants.instDecidableEq (p : ℕ) [Fact (Nat.Prime p)] :
  DecidableEq (SupersingularJInvariants p) := by sorry

/-- The set of supersingular `j`-invariants is nonempty for every prime `p`. -/
theorem SupersingularJInvariants.instNonempty (p : ℕ) [Fact (Nat.Prime p)] :
  Nonempty (SupersingularJInvariants p) := by sorry

attribute [instance] SupersingularJInvariants.instFintype
  SupersingularJInvariants.instDecidableEq
  SupersingularJInvariants.instNonempty

/-- Embed a supersingular `j`-invariant into `ZMod (p^2) ≃ 𝔽_{p^2}`. This realizes
the inclusion of supersingular `j`-invariants into `𝔽_{p^2}` provided by Theorem 13.16. -/
noncomputable def SupersingularJInvariants.toZModPSq (p : ℕ) [Fact (Nat.Prime p)] :
  SupersingularJInvariants p → ZMod (p ^ 2) := by sorry

/-- The embedding of supersingular `j`-invariants into `ZMod (p^2)` is injective. -/
theorem SupersingularJInvariants.toZModPSq_injective (p : ℕ) [Fact (Nat.Prime p)] :
  Function.Injective (SupersingularJInvariants.toZModPSq p) := by sorry

/-- Edges in the `ℓ`-isogeny graph (defined via the modular polynomial `Φ_ℓ`) are symmetric:
if `j₁` is connected to `j₂` then so is `j₂` to `j₁`. This reflects the symmetry of `Φ_ℓ(X, Y)`. -/
theorem modularPolynomial_symmetric_hasEdge
    (k : Type*) [CommRing k] (ℓ : ℕ) (j₁ j₂ : k) :
    IsogenyGraph.hasEdge k ℓ j₁ j₂ → IsogenyGraph.hasEdge k ℓ j₂ j₁ := by sorry

/-- Adjacency in the supersingular `ℓ`-isogeny graph is decidable. -/
noncomputable def supersingularAdj_decidable
    (p ℓ : ℕ) [Fact (Nat.Prime p)] [Fact (Nat.Prime ℓ)]
    (j₁ j₂ : SupersingularJInvariants p) :
    Decidable (j₁ ≠ j₂ ∧
      IsogenyGraph.hasEdge (ZMod (p ^ 2)) ℓ
        (SupersingularJInvariants.toZModPSq p j₁)
        (SupersingularJInvariants.toZModPSq p j₂)) := by sorry

/-- The supersingular `ℓ`-isogeny graph in characteristic `p` (with `p ≠ ℓ`):
a simple graph whose vertices are supersingular `j`-invariants in `𝔽_{p^2}` and
whose edges record the existence of an `ℓ`-isogeny between the corresponding curves
(as detected by the modular polynomial `Φ_ℓ`). -/
def supersingularIsogenyGraph (p ℓ : ℕ) [Fact (Nat.Prime p)] [Fact (Nat.Prime ℓ)]
    (_hne : p ≠ ℓ) : SimpleGraph (SupersingularJInvariants p) where
  Adj j₁ j₂ :=
    j₁ ≠ j₂ ∧
    IsogenyGraph.hasEdge (ZMod (p ^ 2)) ℓ
      (SupersingularJInvariants.toZModPSq p j₁)
      (SupersingularJInvariants.toZModPSq p j₂)
  symm j₁ j₂ := by
    intro ⟨hne_j, hedge⟩
    exact ⟨hne_j.symm,
      modularPolynomial_symmetric_hasEdge (ZMod (p ^ 2)) ℓ _ _ hedge⟩
  loopless := ⟨fun j h => h.1 rfl⟩

/-- The supersingular `ℓ`-isogeny graph is `(ℓ+1)`-regular (as a multigraph): the sum
of edge multiplicities from any vertex `j` to all other vertices equals `ℓ + 1`. -/
theorem supersingularIsogenyGraph_regular_multigraph
    (p ℓ : ℕ) [hp : Fact (Nat.Prime p)] [hℓ : Fact (Nat.Prime ℓ)]
    (hne : p ≠ ℓ) (j : SupersingularJInvariants p) :
    ∑ j' : SupersingularJInvariants p,
      IsogenyGraph.edgeMult (ZMod (p ^ 2)) ℓ
        (SupersingularJInvariants.toZModPSq p j)
        (SupersingularJInvariants.toZModPSq p j') = ℓ + 1 := by sorry

/-- The supersingular `ℓ`-isogeny graph is connected: any two supersingular `j`-invariants
can be linked by a chain of `ℓ`-isogenies. -/
theorem supersingularIsogenyGraph_connected
    (p ℓ : ℕ) [hp : Fact (Nat.Prime p)] [hℓ : Fact (Nat.Prime ℓ)]
    (hne : p ≠ ℓ) :
    (supersingularIsogenyGraph p ℓ hne).Connected := by sorry

/-- `μ` is a nontrivial eigenvalue of the adjacency operator of a `k`-regular graph `G`
(i.e., an eigenvalue other than the trivial eigenvalue `k`). -/
noncomputable def IsNontrivialEigenvalue {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (μ : ℝ) : Prop := by sorry

/-- Pizer/Mestre: the supersingular `ℓ`-isogeny graph is a Ramanujan graph. Every
nontrivial eigenvalue `μ` of its `(ℓ+1)`-regular adjacency operator satisfies
`|μ| ≤ 2√ℓ`, the Ramanujan bound. -/
theorem supersingularIsogenyGraph_ramanujan
    (p ℓ : ℕ) [hp : Fact (Nat.Prime p)] [hℓ : Fact (Nat.Prime ℓ)]
    (hne : p ≠ ℓ) :
    ∀ (μ : ℝ),
      IsNontrivialEigenvalue (supersingularIsogenyGraph p ℓ hne) (ℓ + 1) μ →
      |μ| ≤ 2 * Real.sqrt ℓ := by sorry

end SupersingularIsogenyGraph
