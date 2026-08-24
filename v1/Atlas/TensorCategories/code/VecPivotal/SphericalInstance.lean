/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.VecPivotal.PivotalInstance
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option maxHeartbeats 1600000

open CategoryTheory MonoidalCategory Module Category

universe u

noncomputable section

variable (k : Type u) [Field k]

namespace TensorCategories

/-- For a finite-dimensional vector space `V` over a field `k`, the dimension of `V`
equals the dimension of its dual `V*`. -/
theorem vec_finrank_dual_eq (V : FGModuleCat.{u} k) :
    Module.finrank k V = Module.finrank k (Vᘁ : FGModuleCat.{u} k) :=
  (Subspace.dual_finrank_eq).symm

/-- The pivotal dimension of a finite-dimensional vector space `V` equals
`dim_k(V)` times the identity of the unit object in `FGModuleCat k`. -/
theorem vec_pivotalDimension_eq_finrank_smul_id (V : FGModuleCat.{u} k) :
    pivotalDimension (FGModuleCat.{u} k) V =
      (Module.finrank k V) • (𝟙 (𝟙_ (FGModuleCat.{u} k))) := by
  sorry

/-- The pivotal dimension of the dual `V*` equals `dim_k(V*)` times the
identity of the unit object in `FGModuleCat k`. -/
theorem vec_pivotalDimension_dual_eq_finrank_smul_id (V : FGModuleCat.{u} k) :
    pivotalDimension (FGModuleCat.{u} k) (Vᘁ) =
      (Module.finrank k (Vᘁ : FGModuleCat.{u} k)) • (𝟙 (𝟙_ (FGModuleCat.{u} k))) := by
  sorry

/-- Sphericality of `FGModuleCat k`: the pivotal dimension of `V` agrees with
the pivotal dimension of its dual `V*`. -/
theorem vec_pivotalDimension_dual_eq (V : FGModuleCat.{u} k) :
    pivotalDimension (FGModuleCat.{u} k) V =
      pivotalDimension (FGModuleCat.{u} k) (Vᘁ) := by
  rw [vec_pivotalDimension_eq_finrank_smul_id k V,
      vec_pivotalDimension_dual_eq_finrank_smul_id k V,
      vec_finrank_dual_eq k V]

/-- `FGModuleCat k` is a spherical category (Definition 1.39.1), with sphericality
witnessed by the equality of pivotal dimensions of `V` and `V*`. -/
instance instSphericalCategoryFGModuleCat :
    SphericalCategory (FGModuleCat.{u} k) where
  spherical V := vec_pivotalDimension_dual_eq k V

end TensorCategories

end
