/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic

noncomputable section

/-- **Smoothness via Kähler differentials**: a Noetherian local `k`-algebra `R`
is a regular local ring iff `Ω_{R/k}` is `R`-free. Geometrically, "smooth ⇔ Ω is
locally free of the expected rank". -/
theorem isRegularLocalRing_iff_free_kaehlerDifferential
    (k : Type*) (R : Type*) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] :
    IsRegularLocalRing R ↔ Module.Free R (Ω[R⁄k]) := by
  constructor
  ·


    intro _h
    sorry
  ·

    intro _h
    sorry

open IsLocalRing in
/-- **Remark 28 (Cohen's structure theorem, complete regular local case)**: the
`𝔪`-adic completion of an `n`-dimensional regular local ring `R` is isomorphic
to the formal power series ring `κ[[x₁, …, xₙ]]` over its residue field `κ`. -/
theorem remark28_completed_local_ring_iso_power_series
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hreg : IsRegularLocalRing R)
    (n : ℕ) (hdim : ringKrullDim R = n) :
    Nonempty (AdicCompletion (maximalIdeal R) R ≃+*
      MvPowerSeries (Fin n) (ResidueField R)) := by
  sorry

end
