/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Theorem136
import Atlas.EllipticCurves.code.OrdinarySupersingular

set_option autoImplicit false

/-- Number-theoretic lemma: if `k² = pⁿ` for a prime `p` and natural number `k`,
then `n` is even. Proved by strong induction on `n` using that primes are not
squares. -/
lemma even_of_sq_eq_prime_pow (p : ℕ) (hp : Nat.Prime p) :
    ∀ n k : ℕ, k ^ 2 = p ^ n → Even n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    match n with
    | 0 => exact ⟨0, by omega⟩
    | 1 =>
      exfalso
      simp [pow_one] at hk
      exact Irreducible.not_isSquare hp ⟨k, by rw [← hk]; ring⟩
    | n + 2 =>
      have hpk2 : p ∣ k ^ 2 := ⟨p ^ (n + 1), by rw [hk]; ring⟩
      have hpk : p ∣ k := hp.dvd_of_dvd_pow hpk2
      obtain ⟨j, rfl⟩ := hpk
      have hpn : j ^ 2 = p ^ n := by
        have h1 : (p * j) ^ 2 = p ^ (n + 2) := hk
        have h2 : p ^ 2 * j ^ 2 = p ^ 2 * p ^ n := by
          have : p * p * (j * j) = p * p * p ^ n := by
            calc p * p * (j * j) = (p * j) * (p * j) := by ring
            _ = (p * j) ^ 2 := by ring
            _ = p ^ (n + 2) := h1
            _ = p * p * p ^ n := by ring
          linarith
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.pos_of_ne_zero (pow_ne_zero 2 hp.ne_zero)) h2
      have heven := ih n (by omega) j hpn
      obtain ⟨m, rfl⟩ := heven
      exact ⟨m + 1, by omega⟩

/-- Integer analogue: if an integer satisfies `t² = 4·pⁿ` for a prime `p`, then
`n` is even. This is used to detect when `tr π_E)² = 4q` forces special
behavior over even-degree extensions. -/
lemma even_of_int_sq_eq_four_mul_prime_pow (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (t : ℤ)
    (h : t ^ 2 = 4 * (p ^ n : ℤ)) : Even n := by

  have heven_t : 2 ∣ t := by
    have heven_sq : Even (t ^ 2) := ⟨2 * (p ^ n : ℤ), by omega⟩
    rw [Int.even_pow] at heven_sq
    exact even_iff_two_dvd.mp heven_sq.1

  obtain ⟨k, rfl⟩ := heven_t
  have hk2 : k ^ 2 = (p : ℤ) ^ n := by nlinarith

  have hnat : (k.natAbs) ^ 2 = p ^ n := by
    have h1 : ((k.natAbs : ℤ) ^ 2 : ℤ) = k ^ 2 := Int.natAbs_sq k
    have h2 : ((k.natAbs ^ 2 : ℕ) : ℤ) = (k.natAbs : ℤ) ^ 2 := by push_cast; ring
    have h3 : ((p ^ n : ℕ) : ℤ) = (p : ℤ) ^ n := by push_cast; ring
    exact_mod_cast (show ((k.natAbs ^ 2 : ℕ) : ℤ) = ((p ^ n : ℕ) : ℤ) by
      rw [h2, h1, hk2, h3])
  exact even_of_sq_eq_prime_pow p hp n k.natAbs hnat

open OrdinarySupersingular EndomorphismRingOverFiniteField

section Corollary137_EC

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Under the hypotheses of Corollary 13.7, the Frobenius endomorphism is not
an integer. Concretely: if `#F = pⁿ` and either `n` is odd or `E` is ordinary,
then the Frobenius `π_E` does not satisfy `tr(π_E)² = 4q` (i.e. is not a scalar
multiple of the identity). This is the key technical step toward showing that
`End⁰(E) = ℚ(π_E)` is an imaginary quadratic field. -/
lemma frobeniusNotInt_of_odd_or_ordinary
    (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]
    (n : ℕ) (hcard : Fintype.card F = p ^ n)
    (E : WeierstrassCurve.Affine F)
    (h : Odd n ∨ IsOrdinary E p) :
    frobeniusNotInt E := by


  intro hnotint
  rw [hcard] at hnotint

  have heven : Even n :=
    even_of_int_sq_eq_four_mul_prime_pow p hp.out n _ (by push_cast at hnotint ⊢; exact hnotint)

  have htrace_dvd : (p : ℤ) ∣ Hasse.traceFrobenius E := by
    obtain ⟨m, rfl⟩ := heven

    have hcard_pos : 0 < Fintype.card F := Fintype.card_pos
    rw [hcard] at hcard_pos
    have hp_pos : 1 < p := hp.out.one_lt
    have hm_pos : 0 < m + m := by
      by_contra hle
      simp only [not_lt, Nat.le_zero] at hle

      have hm0 : m = 0 := by omega
      subst hm0
      simp at hcard
      have : 1 < Fintype.card F := Fintype.one_lt_card
      omega
    have hm1 : 1 ≤ m := by omega

    push_cast at hnotint
    have hsq : (Hasse.traceFrobenius E) ^ 2 = (2 * (p : ℤ) ^ m) ^ 2 := by
      rw [hnotint]; ring
    have habs : Hasse.traceFrobenius E = 2 * (p : ℤ) ^ m ∨
                Hasse.traceFrobenius E = -(2 * (p : ℤ) ^ m) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp hsq

    have hpm : (p : ℤ) ∣ (p : ℤ) ^ m := dvd_pow_self (p : ℤ) (by omega : m ≠ 0)
    rcases habs with heq | heq <;> rw [heq]
    · exact dvd_mul_of_dvd_right hpm 2
    · exact dvd_neg.mpr (dvd_mul_of_dvd_right hpm 2)
  have hsuper : IsSupersingular E p :=
    (isSupersingular_iff_trace_dvd p E).mpr htrace_dvd


  rcases h with hodd | hord
  · exact absurd hodd (Nat.not_odd_iff_even.mpr heven)
  · exact (isOrdinary_iff_not_supersingular E p).mp hord hsuper

/-- **Corollary 13.7** (Sutherland §13.1). Let `E` be an elliptic curve over
`𝔽_q` with `q = pⁿ`. If `n` is odd or `E` is ordinary, then
`End⁰(E) = ℚ(π_E) ≃ ℚ(√D)` is an imaginary quadratic field with
`D = (tr π_E)² - 4q`. Concretely we extract three pieces of data:
(1) the Frobenius discriminant is negative;
(2) the endomorphism algebra has `ℚ`-dimension `2`;
(3) it contains an element `α ∉ ℚ` with `α² ∈ ℚ_{<0}` (an imaginary generator). -/
theorem endAlg_imagQuad_of_ordinary_or_odd
    (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]
    (n : ℕ) (hcard : Fintype.card F = p ^ n)
    (E : WeierstrassCurve.Affine F)
    (h : Odd n ∨ IsOrdinary E p) :
    frobeniusDiscriminant E < 0
    ∧ Module.finrank ℚ (EllipticCurve.EndAlgebra E) = 2
    ∧ ∃ α : EllipticCurve.EndAlgebra E,
        (∀ q : ℚ, α ≠ (algebraMap ℚ (EllipticCurve.EndAlgebra E)) q) ∧
        ∃ d : ℚ, d < 0 ∧ α * α =
          (algebraMap ℚ (EllipticCurve.EndAlgebra E)) d := by
  have hnotint := frobeniusNotInt_of_odd_or_ordinary p n hcard E h
  have hq : 0 < Fintype.card F := Fintype.card_pos
  exact ⟨frobeniusDiscriminant_neg E hq hnotint,
         endAlg_finrank_eq_two E hq hnotint,
         endAlg_has_imaginary_generator E hq hnotint⟩

end Corollary137_EC
