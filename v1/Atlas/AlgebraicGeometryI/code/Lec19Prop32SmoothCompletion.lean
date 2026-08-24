/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open IsLocalRing

/-- Proposition 32 (Lecture 19). A Noetherian local `k`-algebra `R` of dimension `d`
with residue field `k` is regular (smooth) iff its `m`-adic completion is isomorphic to the
formal power series ring `k[[t_1,…,t_d]]`. -/
theorem smooth_iff_completion_power_series
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (k : Type*) [Field k] [Algebra k R] (d : ℕ)
    (hdim : ringKrullDim R = d)
    (hres : ResidueField R ≃+* k) :
    IsRegularLocalRing R ↔
      Nonempty (MvPowerSeries (Fin d) k ≃+* AdicCompletion (maximalIdeal R) R) := by
  sorry

/-- A Noetherian local ring is regular iff the dimension of its Zariski cotangent space
matches its Krull dimension. -/
theorem smooth_iff_cotangent_dim
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      ↑(Module.finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R :=
  IsRegularLocalRing.iff_finrank_cotangentSpace R

/-- Numeric form of the regularity criterion: a Noetherian local ring of Krull dimension `d`
is regular iff its cotangent space has dimension `d`. -/
theorem smooth_iff_cotangent_dim_nat
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = d) :
    IsRegularLocalRing R ↔
      Module.finrank (ResidueField R) (CotangentSpace R) = d := by
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hdim, Nat.cast_inj]
