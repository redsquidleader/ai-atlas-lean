/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.QuasiBialgebra
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option maxHeartbeats 800000

universe u v

noncomputable section

/-- A quasi-Hopf subalgebra of a quasi-Hopf algebra H: a subalgebra of H that is stable under
the antipode S of H. -/
structure SubQuasiHopfAlgebra (k : Type u) (H : Type v)
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] where
  toSubalgebra : Subalgebra k H
  antipode_mem : ∀ {x : H}, x ∈ toSubalgebra →
    (QuasiHopfAlgebra.S (R := k) (H := H)) x ∈ toSubalgebra

/-- Allows a `SubQuasiHopfAlgebra` to be treated as a type by coercing to its underlying
subalgebra. -/
instance SubQuasiHopfAlgebra.instSort {k : Type u} {H : Type v}
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] :
    CoeSort (SubQuasiHopfAlgebra k H) (Type v) :=
  ⟨fun K => K.toSubalgebra⟩

/-- The underlying subalgebra of a quasi-Hopf subalgebra carries the natural k-module structure
inherited from H. -/
instance SubQuasiHopfAlgebra.instModuleBase {k : Type u} {H : Type v}
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    (K : SubQuasiHopfAlgebra k H) : Module k K := K.toSubalgebra.module'

/-- The chain of scalar actions k → K → H from a quasi-Hopf subalgebra K of H satisfies the
scalar tower axiom. -/
instance SubQuasiHopfAlgebra.instSTH {k : Type u} {H : Type v}
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    (K : SubQuasiHopfAlgebra k H) : IsScalarTower k K H :=
  Subalgebra.isScalarTower_mid K.toSubalgebra

/-- Corollary 1.50.4 (Nichols-Zoeller for quasi-Hopf algebras): A finite dimensional quasi-Hopf
algebra is a free module over any of its quasi-Hopf subalgebras. -/
theorem corollary_1_50_4 {k : Type u} {H : Type v} [Field k] [Ring H] [Algebra k H]
    [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Module.Free K H := by sorry

/-- Alternative name for `corollary_1_50_4`, emphasizing its identification with the classical
Nichols-Zoeller freeness result in the quasi-Hopf algebra setting. -/
theorem nichols_zoeller_free {k : Type u} {H : Type v} [Field k] [Ring H] [Algebra k H]
    [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Module.Free K H :=
  corollary_1_50_4 K

/-- Uppercase alias for `corollary_1_50_4`, stating Corollary 1.50.4: a finite dimensional
quasi-Hopf algebra is free as a module over its quasi-Hopf subalgebra. -/
theorem Corollary_1_50_4 {k : Type u} {H : Type v} [Field k] [Ring H] [Algebra k H]
    [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Module.Free K H :=
  corollary_1_50_4 K
