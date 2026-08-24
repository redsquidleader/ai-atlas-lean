/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.FiniteType

noncomputable section

universe u v

/-- **Proposition 29, forward direction (auxiliary)**: a Noetherian local ring
that is regular has its module of Kähler differentials `Ω_{R/k}` free over `R`. -/
theorem prop29_regular_implies_omega_free_aux
    (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R]
    (hreg : IsRegularLocalRing R) : Module.Free R (Ω[R⁄k]) := by sorry

/-- **Proposition 29, reverse direction (auxiliary)**: if `Ω_{R/k}` is free over
a Noetherian local `k`-algebra `R`, then `R` is regular. -/
theorem prop29_omega_free_implies_regular_aux
    (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R]
    (hfree : Module.Free R (Ω[R⁄k])) : IsRegularLocalRing R := by sorry

/-- **Proposition 29 (smooth ⇔ Ω is locally free)**: a Noetherian local `k`-algebra
`R` is regular iff `Ω_{R/k}` is `R`-free. The geometric statement: a finite-type
`k`-scheme is smooth at a point iff its sheaf of differentials is locally free
there. -/
theorem prop29_smooth_iff_omega_locally_free
    (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] :
    IsRegularLocalRing R ↔ Module.Free R (Ω[R⁄k]) :=
  ⟨prop29_regular_implies_omega_free_aux k R,
   prop29_omega_free_implies_regular_aux k R⟩

/-- Universe-polymorphic restatement of `prop29_smooth_iff_omega_locally_free`. -/
theorem smooth_iff_omega_locally_free
    (k R : Type*) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] :
    IsRegularLocalRing R ↔ Module.Free R (Ω[R⁄k]) :=
  prop29_smooth_iff_omega_locally_free k R

/-- The forward direction of Proposition 29, extracted via the iff. -/
theorem prop29_regular_implies_omega_free
    (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R]
    (hreg : IsRegularLocalRing R) : Module.Free R (Ω[R⁄k]) :=
  (prop29_smooth_iff_omega_locally_free k R).mp hreg

/-- The reverse direction of Proposition 29, extracted via the iff. -/
theorem prop29_omega_free_implies_regular
    (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R]
    (hfree : Module.Free R (Ω[R⁄k])) : IsRegularLocalRing R :=
  (prop29_smooth_iff_omega_locally_free k R).mpr hfree

/-- **Localized version of Proposition 29**: for a finite-type integral domain `A`
over `k` and a prime ideal `𝔭`, the localization `A_𝔭` is regular iff
`Ω_{A_𝔭 / k}` is `A_𝔭`-free. -/
theorem prop29_localization_smooth_iff_omega_free
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (𝔭 : Ideal A) [𝔭.IsPrime]
    [IsNoetherianRing (Localization.AtPrime 𝔭)] :
    IsRegularLocalRing (Localization.AtPrime 𝔭) ↔
      Module.Free (Localization.AtPrime 𝔭) (Ω[Localization.AtPrime 𝔭⁄k]) :=
  prop29_smooth_iff_omega_locally_free k (Localization.AtPrime 𝔭)

end
