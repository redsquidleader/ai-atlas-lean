/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HopfAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.RepresentationTheory.FDRep

set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section Corollary_1_22_6

open CategoryTheory


/-- Corollary 1.22.6(i): if `H` is a bialgebra with an antipode `S`, then the abelian monoidal
category `Rep(H)` has right duals — namely the linear dual `V^*` with `H`-action via
`ρ_{V^*}(a) = ρ_V(S(a))^*`. -/
@[reducible]
noncomputable def Corollary_1_22_6
    (k : Type u) [Field k] (H : Type v) [Ring H] [HopfAlgebra k H]
    [MonoidalCategory (ModuleCat.{v} H)] :
    RightRigidCategory (ModuleCat.{v} H) :=
  sorry


/-- Corollary 1.22.6(ii): if in addition the antipode `S` of `H` is invertible, then `Rep(H)`
also admits left duals, i.e. is rigid (and hence a tensor category). The left dual `*V` is the
dual space with `H`-action `ρ_{*V}(a) = ρ_V(S^{-1}(a))^*`. -/
@[reducible]
noncomputable def Corollary_1_22_6_rigid
    (k : Type u) [Field k] (H : Type v) [Ring H] [HopfAlgebra k H]
    (hS : Function.Bijective (HopfAlgebra.antipode k : H →ₗ[k] H))
    [MonoidalCategory (ModuleCat.{v} H)] :
    RigidCategory (ModuleCat.{v} H) :=
  sorry

/-- Instance of Corollary 1.22.6(i) for a group algebra: `FDRep k G` is right-rigid. -/
noncomputable instance Corollary_1_22_6_right_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RightRigidCategory (FDRep k G) :=
  inferInstance

/-- Instance of Corollary 1.22.6(ii) for a group algebra: `FDRep k G` is rigid (i.e. a
tensor category). -/
noncomputable instance Corollary_1_22_6_rigid_group
    (k G : Type u) [Field k] [Group G] :
    RigidCategory (FDRep k G) :=
  inferInstance

end Corollary_1_22_6
