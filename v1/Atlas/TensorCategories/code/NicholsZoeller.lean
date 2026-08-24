/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Atlas.TensorCategories.code.QuasiBialgebra

set_option maxHeartbeats 800000

universe u v

noncomputable section


/-- A sub-quasi-Hopf-algebra of `H`: a `k`-subalgebra closed under the antipode. -/
structure SubQuasiHopfAlgebra (k : Type u) (H : Type v)
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] where
  toSubalgebra : Subalgebra k H
  antipode_mem : ∀ {x : H}, x ∈ toSubalgebra →
    (QuasiHopfAlgebra.S (R := k) (H := H)) x ∈ toSubalgebra

section SubQuasiHopfAlgebraInstances

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]

/-- Coerce a `SubQuasiHopfAlgebra` to its underlying `Subalgebra`. -/
instance SubQuasiHopfAlgebra.instCoe : CoeOut (SubQuasiHopfAlgebra k H) (Subalgebra k H) :=
  ⟨SubQuasiHopfAlgebra.toSubalgebra⟩

/-- View a `SubQuasiHopfAlgebra` as a type via its underlying subalgebra. -/
instance SubQuasiHopfAlgebra.instSort : CoeSort (SubQuasiHopfAlgebra k H) (Type v) :=
  ⟨fun K => K.toSubalgebra⟩

variable (K : SubQuasiHopfAlgebra k H)

/-- The base-field `k`-module structure on a sub-quasi-Hopf algebra `K`. -/
instance SubQuasiHopfAlgebra.instModuleBase : Module k K := K.toSubalgebra.module'

/-- Scalar tower `k → K → H` for a sub-quasi-Hopf algebra `K ⊆ H`. -/
instance SubQuasiHopfAlgebra.instSTH : IsScalarTower k K H :=
  Subalgebra.isScalarTower_mid K.toSubalgebra

/-- A sub-quasi-Hopf-algebra over a field is free as a module over the base field. -/
instance SubQuasiHopfAlgebra.instFreekK : Module.Free k K :=
  Module.Free.of_divisionRing k K

/-- A quasi-Hopf algebra over a field is nontrivial. -/
lemma QuasiHopfAlgebra.nontrivial_of_field
    (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] :
    Nontrivial H := by
  sorry

/-- A sub-quasi-Hopf algebra over a field is nontrivial. -/
lemma SubQuasiHopfAlgebra.nontrivial_carrier : Nontrivial K := by
  sorry

variable [FiniteDimensional k H]

/-- A sub-quasi-Hopf algebra of a finite-dimensional quasi-Hopf algebra is itself
finite-dimensional. -/
instance SubQuasiHopfAlgebra.instFinDim : FiniteDimensional k K :=
  FiniteDimensional.finiteDimensional_submodule K.toSubalgebra.toSubmodule

/-- The dimension of a sub-quasi-Hopf algebra over the base field is strictly positive. -/
lemma SubQuasiHopfAlgebra.finrank_pos : 0 < Module.finrank k K := by
  haveI := SubQuasiHopfAlgebra.nontrivial_carrier k H K
  exact Module.finrank_pos

end SubQuasiHopfAlgebraInstances

/-- EGNO Corollary 1.50.4: a finite-dimensional quasi-Hopf algebra `H` is free as a module
over any sub-quasi-Hopf algebra `K`. -/
theorem corollary_1_50_4 {k : Type u} {H : Type v} [Field k] [Ring H] [Algebra k H]
    [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Module.Free K H := by
  sorry

/-- Nichols-Zoeller for quasi-Hopf algebras: freeness of `H` over any sub-quasi-Hopf
algebra `K`. -/
theorem nichols_zoeller_free {k : Type u} {H : Type v} [Field k] [Ring H] [Algebra k H]
    [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Module.Free K H :=
  corollary_1_50_4 K

/-- A sub-quasi-Hopf algebra of a finite-dimensional quasi-Hopf algebra satisfies the
strong rank condition. -/
theorem strongRankCondition_subQuasiHopfAlgebra {k : Type u} {H : Type v}
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : StrongRankCondition K := by
  haveI : Nontrivial K := SubQuasiHopfAlgebra.nontrivial_carrier k H K
  haveI : IsNoetherianRing K := IsNoetherianRing.of_finite k K
  exact IsNoetherianRing.strongRankCondition K

/-- Bundle of consequences of Nichols-Zoeller for a sub-quasi-Hopf algebra `K ⊆ H`:
freeness, finiteness, and divisibility of dimensions. -/
class QuasiHopfFreeness (k : Type u) (H : Type v)
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Prop where
  free : Module.Free K H
  finite : Module.Finite K H
  finrank_dvd : Module.finrank k K ∣ Module.finrank k H

section QuasiHopfFreenessInstance

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    [FiniteDimensional k H] (K : SubQuasiHopfAlgebra k H)

/-- `H` is module-finite over any sub-quasi-Hopf algebra `K`, inherited from
finite-dimensionality over the base field. -/
theorem SubQuasiHopfAlgebra.module_finite_KH : Module.Finite K H :=
  Module.Finite.of_restrictScalars_finite k K H

/-- The dimension of a sub-quasi-Hopf algebra divides the dimension of the ambient
quasi-Hopf algebra, derived from freeness via Nichols-Zoeller. -/
theorem SubQuasiHopfAlgebra.finrank_dvd_of_free :
    Module.finrank k K ∣ Module.finrank k H := by
  haveI : Module.Free K H := corollary_1_50_4 K
  haveI : Module.Finite K H := Module.Finite.of_restrictScalars_finite k K H
  haveI : StrongRankCondition K := strongRankCondition_subQuasiHopfAlgebra K
  have hmul := @Module.finrank_mul_finrank k K H _ _ _
    (SubQuasiHopfAlgebra.instModuleBase k H K) _ _
    (SubQuasiHopfAlgebra.instSTH k H K) _ _
    (SubQuasiHopfAlgebra.instFreekK k H K) _
  exact ⟨Module.finrank K H, hmul.symm⟩

/-- The Nichols-Zoeller consequences `QuasiHopfFreeness` are automatically available for
any sub-quasi-Hopf algebra of a finite-dimensional quasi-Hopf algebra. -/
instance SubQuasiHopfAlgebra.instQuasiHopfFreeness : QuasiHopfFreeness k H K where
  free := corollary_1_50_4 K
  finite := SubQuasiHopfAlgebra.module_finite_KH k H K
  finrank_dvd := SubQuasiHopfAlgebra.finrank_dvd_of_free k H K

end QuasiHopfFreenessInstance

section QuasiHopfFreenessConsequences

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) [QuasiHopfFreeness k H K]

/-- Extract freeness of `H` over `K` from the `QuasiHopfFreeness` bundle. -/
theorem QuasiHopfFreeness.free' : Module.Free K H :=
  QuasiHopfFreeness.free

/-- Extract module-finiteness of `H` over `K` from the `QuasiHopfFreeness` bundle. -/
theorem QuasiHopfFreeness.finite' : Module.Finite K H :=
  QuasiHopfFreeness.finite

/-- Extract dimension divisibility from the `QuasiHopfFreeness` bundle. -/
theorem QuasiHopfFreeness.finrank_dvd' :
    Module.finrank k K ∣ Module.finrank k H :=
  QuasiHopfFreeness.finrank_dvd

/-- The dimension of a sub-quasi-Hopf algebra is at most the dimension of the ambient
quasi-Hopf algebra. -/
theorem QuasiHopfFreeness.finrank_le :
    Module.finrank k K ≤ Module.finrank k H := by
  sorry

end QuasiHopfFreenessConsequences


/-- A Hopf algebra over a field is nontrivial: the counit distinguishes `0` and `1`. -/
lemma HopfAlgebra.nontrivial_of_field (k : Type u) (H : Type v)
    [Field k] [Ring H] [HopfAlgebra k H] : Nontrivial H :=
  ⟨⟨0, 1, fun h => by
    have := congr_arg (Bialgebra.counitAlgHom k H) h; simp at this⟩⟩

/-- A sub-Hopf-algebra of `H`: a `k`-subalgebra closed under the antipode. -/
structure SubHopfAlgebra (k : Type u) (H : Type v)
    [Field k] [Ring H] [HopfAlgebra k H] where
  toSubalgebra : Subalgebra k H
  antipode_mem : ∀ {x : H}, x ∈ toSubalgebra → HopfAlgebra.antipode k x ∈ toSubalgebra

section SubHopfAlgebraInstances

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]

/-- Coerce a `SubHopfAlgebra` to its underlying `Subalgebra`. -/
instance SubHopfAlgebra.instCoe : CoeOut (SubHopfAlgebra k H) (Subalgebra k H) :=
  ⟨SubHopfAlgebra.toSubalgebra⟩

/-- View a `SubHopfAlgebra` as a type via its underlying subalgebra. -/
instance SubHopfAlgebra.instSort : CoeSort (SubHopfAlgebra k H) (Type v) :=
  ⟨fun K => K.toSubalgebra⟩

variable (K : SubHopfAlgebra k H)

/-- The base-field `k`-module structure on a sub-Hopf algebra `K`. -/
instance SubHopfAlgebra.instModuleBase : Module k K := K.toSubalgebra.module'

/-- Scalar tower `k → K → H` for a sub-Hopf algebra `K ⊆ H`. -/
instance SubHopfAlgebra.instSTH : IsScalarTower k K H :=
  Subalgebra.isScalarTower_mid K.toSubalgebra

/-- A sub-Hopf algebra over a field is free as a module over the base field. -/
instance SubHopfAlgebra.instFreekK : Module.Free k K :=
  Module.Free.of_divisionRing k K

/-- A sub-Hopf algebra of a nontrivial Hopf algebra over a field is itself nontrivial. -/
lemma SubHopfAlgebra.nontrivial_carrier : Nontrivial K := by
  haveI : Nontrivial H := HopfAlgebra.nontrivial_of_field k H
  exact ⟨⟨⟨0, K.toSubalgebra.zero_mem⟩, ⟨1, K.toSubalgebra.one_mem⟩,
    fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩

variable [FiniteDimensional k H]

/-- A sub-Hopf algebra of a finite-dimensional Hopf algebra is itself finite-dimensional. -/
instance SubHopfAlgebra.instFinDim : FiniteDimensional k K :=
  FiniteDimensional.finiteDimensional_submodule K.toSubalgebra.toSubmodule

/-- The dimension of a sub-Hopf algebra over the base field is strictly positive. -/
lemma SubHopfAlgebra.finrank_pos : 0 < Module.finrank k K := by
  haveI := SubHopfAlgebra.nontrivial_carrier k H K
  exact Module.finrank_pos

end SubHopfAlgebraInstances

/-- A sub-Hopf algebra of a finite-dimensional Hopf algebra satisfies the strong rank
condition. -/
theorem strongRankCondition_subHopfAlgebra {k : Type u} {H : Type v}
    [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]
    (K : SubHopfAlgebra k H) : StrongRankCondition K := by
  haveI : Nontrivial K := SubHopfAlgebra.nontrivial_carrier k H K
  haveI : IsNoetherianRing K := IsNoetherianRing.of_finite k K
  exact IsNoetherianRing.strongRankCondition K

/-- Nichols-Zoeller bundle for a sub-Hopf algebra `K ⊆ H` of a finite-dimensional Hopf
algebra: freeness, finiteness, and divisibility of dimensions. -/
class NicholsZoellerFreeness (k : Type u) (H : Type v)
    [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]
    (K : SubHopfAlgebra k H) : Prop where
  free : Module.Free K H
  finite : Module.Finite K H
  finrank_dvd : Module.finrank k K ∣ Module.finrank k H

section NicholsZoellerHelpers

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]
    [FiniteDimensional k H] (K : SubHopfAlgebra k H)

/-- `H` is module-finite over any sub-Hopf algebra `K`, inherited from finite-dimensionality
over the base field. -/
theorem SubHopfAlgebra.module_finite_KH : Module.Finite K H :=
  Module.Finite.of_restrictScalars_finite k K H

/-- If `H` is free over a sub-Hopf algebra `K`, then `dim_k K` divides `dim_k H`. -/
theorem SubHopfAlgebra.finrank_dvd_of_free (hfree : Module.Free K H) :
    Module.finrank k K ∣ Module.finrank k H := by
  haveI : Module.Free K H := hfree
  haveI : Module.Finite K H := Module.Finite.of_restrictScalars_finite k K H
  haveI : StrongRankCondition K := strongRankCondition_subHopfAlgebra K
  have hmul := @Module.finrank_mul_finrank k K H _ _ _
    (SubHopfAlgebra.instModuleBase k H K) _ _
    (SubHopfAlgebra.instSTH k H K) _ _
    (SubHopfAlgebra.instFreekK k H K) _
  exact ⟨Module.finrank K H, hmul.symm⟩

end NicholsZoellerHelpers

section NicholsZoellerConsequences

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]
    [FiniteDimensional k H]
    (K : SubHopfAlgebra k H) [NicholsZoellerFreeness k H K]

/-- Extract Nichols-Zoeller freeness from the `NicholsZoellerFreeness` bundle. -/
theorem NicholsZoeller.free : Module.Free K H :=
  NicholsZoellerFreeness.free

/-- Extract module-finiteness from the `NicholsZoellerFreeness` bundle. -/
theorem NicholsZoeller.finite : Module.Finite K H :=
  NicholsZoellerFreeness.finite

/-- Extract dimension divisibility from the `NicholsZoellerFreeness` bundle. -/
theorem NicholsZoeller.finrank_dvd :
    Module.finrank k K ∣ Module.finrank k H :=
  NicholsZoellerFreeness.finrank_dvd

/-- The dimension of a sub-Hopf algebra is at most the dimension of the ambient Hopf
algebra. -/
theorem NicholsZoeller.finrank_le :
    Module.finrank k K ≤ Module.finrank k H := by
  have hpos : 0 < Module.finrank k H := by
    haveI : Nontrivial H := HopfAlgebra.nontrivial_of_field k H
    exact Module.finrank_pos
  exact Nat.le_of_dvd hpos (NicholsZoeller.finrank_dvd k H K)

/-- The integer quotient `dim_k H / dim_k K` is strictly positive. -/
theorem NicholsZoeller.finrank_div_pos :
    0 < Module.finrank k H / Module.finrank k K := by
  have hK := SubHopfAlgebra.finrank_pos k H K
  have hdvd := NicholsZoeller.finrank_dvd k H K
  have hH : 0 < Module.finrank k H := by
    haveI : Nontrivial H := HopfAlgebra.nontrivial_of_field k H
    exact Module.finrank_pos
  exact Nat.div_pos (Nat.le_of_dvd hH hdvd) hK

/-- Dimension identity `dim_k H = dim_k K * (dim_k H / dim_k K)` resulting from the
divisibility statement of Nichols-Zoeller. -/
theorem NicholsZoeller.finrank_eq_mul_div :
    Module.finrank k H = Module.finrank k K * (Module.finrank k H / Module.finrank k K) :=
  Nat.eq_mul_of_div_eq_right (NicholsZoeller.finrank_dvd k H K) rfl

end NicholsZoellerConsequences
