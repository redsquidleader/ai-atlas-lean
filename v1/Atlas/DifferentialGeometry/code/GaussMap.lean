/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialGeometry.code.Manifolds
import Mathlib.Topology.Connected.Basic

noncomputable section

open Metric Set

namespace GaussMap

variable {n : ℕ}

abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1


theorem smooth_local_diffeo_compact_to_sphere_bijective
  (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
  (hM_hyp : Hypersurface.IsHypersurface M)
  (hM_compact : IsCompact M)
  (hM_connected : IsConnected M)
  (hn : 2 ≤ n)
  (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
  (hφ_maps : ∀ y ∈ M, φ y ∈ unitSphere n)
  (hφ_smooth : ContDiffOn ℝ ⊤ φ M)
  (hφ_tangent_iso : ∀ y ∈ M, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    Hypersurface.IsLocalDefiningFunction ψ M y →
      ∀ v ∈ Hypersurface.tangentSpace ψ y, fderiv ℝ φ y v = 0 → v = 0)
  : Function.Bijective (fun (y : M) => (⟨φ y, hφ_maps y y.2⟩ : unitSphere n)) := by sorry

end GaussMap
