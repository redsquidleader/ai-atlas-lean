/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Jacobson.Radical

set_option maxHeartbeats 800000

open TensorProduct

universe u v w

noncomputable section

/-- General form of Chevalley's theorem in characteristic zero: the tensor product over `k`
of two semisimple `H`-modules `V` and `W` over a cocommutative Hopf algebra `H` is again
semisimple. -/
theorem tensor_semisimple_of_semisimple_char_zero
    (k : Type u) [Field k] [CharZero k]
    (H : Type v) [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
    (V : Type w) [AddCommGroup V] [Module k V] [Module H V] [IsScalarTower k H V]
    [Module.Finite k V]
    (W : Type w) [AddCommGroup W] [Module k W] [Module H W] [IsScalarTower k H W]
    [Module.Finite k W]
    [Module H (V ⊗[k] W)] [IsScalarTower k H (V ⊗[k] W)]
    (hV : IsSemisimpleModule H V)
    (hW : IsSemisimpleModule H W) :
    IsSemisimpleModule H (V ⊗[k] W) := by
  sorry

/-- Theorem 1.30.1 (Chevalley): Over a field `k` of characteristic zero, the tensor product
of two simple finite-dimensional `H`-modules (for `H` a cocommutative Hopf algebra) is
semisimple. -/
theorem chevalley_tensor_semisimple
    (k : Type u) [Field k] [CharZero k]
    (H : Type v) [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
    (V : Type w) [AddCommGroup V] [Module k V] [Module H V] [IsScalarTower k H V]
    [Module.Finite k V] [IsSimpleModule H V]
    (W : Type w) [AddCommGroup W] [Module k W] [Module H W] [IsScalarTower k H W]
    [Module.Finite k W] [IsSimpleModule H W]
    [Module H (V ⊗[k] W)] [IsScalarTower k H (V ⊗[k] W)] :
    IsSemisimpleModule H (V ⊗[k] W) := by

  have hV_ss : IsSemisimpleModule H V := inferInstance

  have hW_ss : IsSemisimpleModule H W := inferInstance


  exact tensor_semisimple_of_semisimple_char_zero k H V W hV_ss hW_ss

/-- Reformulation of Chevalley's theorem: the Jacobson radical of the tensor product
`V ⊗ W` of two simple modules over a cocommutative Hopf algebra in characteristic zero is
trivial. -/
theorem chevalley_tensor_jacobson_eq_bot
    (k : Type u) [Field k] [CharZero k]
    (H : Type v) [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
    (V : Type w) [AddCommGroup V] [Module k V] [Module H V] [IsScalarTower k H V]
    [Module.Finite k V] [IsSimpleModule H V]
    (W : Type w) [AddCommGroup W] [Module k W] [Module H W] [IsScalarTower k H W]
    [Module.Finite k W] [IsSimpleModule H W]
    [Module H (V ⊗[k] W)] [IsScalarTower k H (V ⊗[k] W)] :
    Module.jacobson H (V ⊗[k] W) = ⊥ := by
  haveI := chevalley_tensor_semisimple k H V W
  sorry

/-- Maschke's theorem for finite commutative groups in characteristic zero: the group
algebra `k[G]` is a semisimple ring. -/
theorem MonoidAlgebra.instIsSemisimpleRing_of_finite
    (k : Type*) [Field k] [CharZero k]
    (G : Type*) [CommGroup G] [Finite G] :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  have : NeZero (Nat.card G : k) := by
    constructor
    exact_mod_cast Nat.card_pos.ne'
  exact inferInstance

/-- Any finite dimensional module over the group algebra `k[G]` of a finite commutative
group in characteristic zero is semisimple. -/
theorem MonoidAlgebra.finiteDim_isSemisimpleModule_of_finite
    (k : Type*) [Field k] [CharZero k]
    (G : Type*) [CommGroup G] [Finite G]
    (M : Type*) [AddCommGroup M] [Module k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]
    [Module.Finite k M] :
    IsSemisimpleModule (MonoidAlgebra k G) M := by
  have : NeZero (Nat.card G : k) := by
    constructor
    exact_mod_cast Nat.card_pos.ne'
  have : IsSemisimpleRing (MonoidAlgebra k G) := inferInstance
  exact IsSemisimpleRing.isSemisimpleModule

example (k : Type*) [Field k] [CharZero k] (G : Type*) [CommGroup G] :
    HopfAlgebra k (MonoidAlgebra k G) := inferInstance

example (k : Type*) [Field k] [CharZero k] (G : Type*) [CommGroup G] :
    Coalgebra.IsCocomm k (MonoidAlgebra k G) := inferInstance

end
