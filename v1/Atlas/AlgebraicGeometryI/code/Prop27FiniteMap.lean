/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Over
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Normalization

open AlgebraicGeometry CategoryTheory

universe u

/-- A morphism between two proper `k`-schemes that is itself compatible with the
structure maps is proper. -/
theorem prop27_isProper
    (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))]
    (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] :
    IsProper f := by
  have h : f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k) := HomIsOver.comp_over
  haveI : IsProper (f ≫ (Y ↘ Spec (.of k))) := h ▸ inferInstance
  exact IsProper.of_comp f (Y ↘ Spec (.of k))

/-- Lemma 29: for a dominant proper morphism of integral schemes, the induced map to
the normalization of `Y` is an isomorphism. -/
theorem lemma_29_toNormalization_isIso
    (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))]
    (f : X ⟶ Y)
    [IsDominant f]
    [IsProper f] :
    IsIso f.toNormalization := by sorry

/-- Proposition 28: for a dominant proper morphism of integral schemes, the canonical
map from the normalization back to `Y` is finite. -/
theorem prop_28_fromNormalization_isFinite
    (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))]
    (f : X ⟶ Y)
    [IsDominant f]
    [IsProper f] :
    IsFinite f.fromNormalization := by sorry

/-- Proposition 27: a non-constant (dominant) morphism between irreducible proper
curves over `k` is finite. -/
theorem prop27_nonconstant_map_finite
    {k : Type u} [Field k]
    {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))]
    (_hdimX : topologicalKrullDim X = 1)
    (_hdimY : topologicalKrullDim Y = 1)
    (f : X ⟶ Y)
    [IsDominant f]
    [f.IsOver (Spec (.of k))]
    : IsFinite f := by

  haveI : IsProper f := prop27_isProper k f

  haveI : IsIso f.toNormalization := lemma_29_toNormalization_isIso k f

  haveI : IsFinite f.fromNormalization := prop_28_fromNormalization_isFinite k f

  rw [← f.toNormalization_fromNormalization]
  infer_instance
