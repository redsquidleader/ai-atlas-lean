/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.RegularLocalRing.Defs

set_option backward.isDefEq.respectTransparency false

namespace PowerSeriesUFD

variable (k : Type*) [Field k]

/-- The maximal ideal of k[[x]] is the principal ideal (x). -/
theorem maximalIdeal_eq_span_X' :
    IsLocalRing.maximalIdeal (PowerSeries k) =
      Ideal.span {(PowerSeries.X : PowerSeries k)} :=
  PowerSeries.maximalIdeal_eq_span_X

/-- The power series ring k[[x_1,...,x_n]] is an integral domain. -/
instance mvPowerSeries_fin_isDomain (n : ℕ) : IsDomain (MvPowerSeries (Fin n) k) :=
  NoZeroDivisors.to_isDomain _

/-- The power series ring k[[x_1,...,x_n]] is a local ring. -/
instance mvPowerSeries_fin_isLocalRing (n : ℕ) : IsLocalRing (MvPowerSeries (Fin n) k) :=
  inferInstance

/-- Auslander-Buchsbaum theorem: every regular local ring is a UFD. -/
theorem regularLocalRing_isUFD (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R := by sorry

/-- The power series ring k[[x_1,...,x_n]] is a regular local ring. -/
theorem mvPowerSeries_isRegularLocalRing (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) k) := by sorry

/-- The power series ring k[[x_1,...,x_n]] is a UFD (Proposition 23, Lecture 15). -/
instance mvPowerSeries_isUFD (n : ℕ) :
    UniqueFactorizationMonoid (MvPowerSeries (Fin n) k) := by
  haveI := mvPowerSeries_isRegularLocalRing k n
  exact regularLocalRing_isUFD (MvPowerSeries (Fin n) k)

/-- Descent: a Noetherian local domain whose completion is a UFD is itself a UFD
(Proposition 23, Lecture 15). -/
theorem ufd_of_completion_ufd
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (hcompl : UniqueFactorizationMonoid
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    UniqueFactorizationMonoid A := by sorry

variable {K : Type*} [Field K]

end PowerSeriesUFD
