/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs

set_option autoImplicit false

section Prop23

variable (k : Type*) [Field k]

/-- The formal power series ring `k[[x_1, ..., x_n]]` over a field is a domain. -/
instance mvPowerSeries_fin_isDomain' (n : ℕ) : IsDomain (MvPowerSeries (Fin n) k) :=
  NoZeroDivisors.to_isDomain _

/-- Auslander–Buchsbaum: every regular local ring (which is a domain) is a UFD. -/
theorem auslander_buchsbaum_UFD
    (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R := by sorry

/-- `k[[x_1, ..., x_n]]` is a regular local ring. -/
theorem mvPowerSeries_fin_isRegularLocalRing
    (n : ℕ) : IsRegularLocalRing (MvPowerSeries (Fin n) k) := by sorry

/-- Proposition 23 (a): the formal power series ring `k[[x_1, ..., x_n]]` over a field
is a UFD. -/
theorem prop23_power_series_UFD
    (n : ℕ) :
    UniqueFactorizationMonoid (MvPowerSeries (Fin n) k) := by
  haveI := mvPowerSeries_fin_isRegularLocalRing k n
  exact auslander_buchsbaum_UFD (MvPowerSeries (Fin n) k)

/-- Proposition 23 (b): if a Noetherian local domain `A` has UFD completion, then `A`
itself is a UFD. -/
theorem prop23_UFD_of_completion_UFD
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (hUFD : UniqueFactorizationMonoid (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    UniqueFactorizationMonoid A := by sorry

end Prop23
