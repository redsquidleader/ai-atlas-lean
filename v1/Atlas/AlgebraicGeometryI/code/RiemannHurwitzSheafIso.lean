/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization

open Ideal UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace RiemannHurwitzSheaf

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- The different ideal `𝔡_{B/A}` is divisible by `P^{e_P - 1}` for each prime
`P` above a non-zero maximal ideal `p` of `A`. -/
theorem differentIdeal_dvd_pow_sub_one
    {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) :
    P ^ (p.ramificationIdx P - 1) ∣ differentIdeal A B :=
  pow_sub_one_dvd_differentIdeal A P (p.ramificationIdx P) hp
    (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)

/-- In the tame case, `P^{e_P}` does not divide the different ideal `𝔡_{B/A}`,
so the exponent of `P` in `𝔡_{B/A}` is exactly `e_P - 1`. -/
theorem not_dvd_pow_ramificationIdx_of_tame
    {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) (hP : P ≠ ⊥)
    (he : p.ramificationIdx P ≠ 0)
    (htame : Nat.Coprime (p.ramificationIdx P) (ringChar (B ⧸ P))) :
    ¬ P ^ (p.ramificationIdx P) ∣ differentIdeal A B := by
  rw [Ideal.dvd_iff_le]


  sorry

/-- In the tame case, the multiplicity of `P` in the different ideal `𝔡_{B/A}`
is exactly `e_P - 1`. This is the local model behind Riemann–Hurwitz. -/
theorem differentIdeal_count_eq_ramificationIdx_sub_one
    {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) (hP : P ≠ ⊥)
    (he : p.ramificationIdx P ≠ 0)
    (htame : Nat.Coprime (p.ramificationIdx P) (ringChar (B ⧸ P))) :
    Multiset.count P (normalizedFactors (differentIdeal A B)) =
      p.ramificationIdx P - 1 := by
  apply Ideal.count_normalizedFactors_eq
  ·
    exact Ideal.dvd_iff_le.mp (differentIdeal_dvd_pow_sub_one A hp)
  ·
    rw [show p.ramificationIdx P - 1 + 1 = p.ramificationIdx P from
      Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero he)]
    exact fun h => not_dvd_pow_ramificationIdx_of_tame A hp hP he htame
      (Ideal.dvd_iff_le.mpr h)

/-- Combined statement of the two divisibility facts: `P^{e_P - 1}` divides
the different ideal but `P^{e_P}` does not (in the tame case). -/
theorem differentIdeal_exact_pow
    {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) (hP : P ≠ ⊥)
    (he : p.ramificationIdx P ≠ 0)
    (htame : Nat.Coprime (p.ramificationIdx P) (ringChar (B ⧸ P))) :
    P ^ (p.ramificationIdx P - 1) ∣ differentIdeal A B ∧
    ¬ P ^ (p.ramificationIdx P) ∣ differentIdeal A B :=
  ⟨differentIdeal_dvd_pow_sub_one A hp,
   not_dvd_pow_ramificationIdx_of_tame A hp hP he htame⟩

end RiemannHurwitzSheaf
