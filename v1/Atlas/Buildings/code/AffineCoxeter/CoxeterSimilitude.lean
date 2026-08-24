/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.CanonicalMetric

set_option maxHeartbeats 400000

open scoped InnerProductSpace
open Set

noncomputable section

namespace AffineCoxeter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Corollary: any simplicial isomorphism between affine Coxeter complexes that lifts to an affine
map of the ambient Euclidean spaces is a **similitude** with scaling factor $\mu > 0$ matching
the ratio of chamber diameters. -/
theorem cor_affine_coxeter_similitude
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (f : E →ᵃ[ℝ] E')
    (hf_compat : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
    ∃ (μ : ℝ), μ > 0
      ∧ (∀ x y : E, euclideanDist (E := E') (f x) (f y) = μ * euclideanDist x y)
      ∧ A'.chamberDiameter = μ * A.chamberDiameter :=
  simplicial_iso_is_similitude_with_diameter A A' φ f hf_compat

/-- Corollary: after normalizing each Euclidean metric by the chamber diameter, the simplicial
isomorphism becomes a true **isometry**: $d_{A'}(f x, f y) = d_A(x, y)$. -/
theorem cor_affine_coxeter_isometry_normalized
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (f : E →ᵃ[ℝ] E')
    (hf_compat : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
    ∀ x y : E, normalizedDist A' (f x) (f y) = normalizedDist A x y :=
  canonical_metric_isometry A A' φ f hf_compat

end AffineCoxeter

end
