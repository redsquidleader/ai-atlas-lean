/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

noncomputable section

open Nat MvPolynomial

/-- The cardinality of `Fin k → ℕ` tuples summing to `n` equals
`multichoose k n`. -/
theorem card_antidiagonalTuple (k n : ℕ) :
    (Finset.Nat.antidiagonalTuple k n).card = Nat.multichoose k n := by
  change (List.Nat.antidiagonalTuple k n).length = Nat.multichoose k n
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [List.Nat.antidiagonalTuple_zero_zero]
    | succ n => simp [List.Nat.antidiagonalTuple_zero_succ]
  | succ k ih =>
    show (List.Nat.antidiagonalTuple (k + 1) n).length = _
    unfold List.Nat.antidiagonalTuple
    rw [List.length_flatMap]
    simp only [List.length_map, ih]
    show (List.map (fun a => k.multichoose a.2)
      (List.map (fun i => (i, n - i)) (List.range (n + 1)))).sum = _
    rw [List.map_map]
    simp only [Function.comp_def]
    have h1 : (List.map (fun i => Nat.multichoose k (n - i)) (List.range (n + 1))).sum =
        ∑ i ∈ Finset.range (n + 1), Nat.multichoose k (n - i) := by
      show _ = (Finset.range (n + 1)).sum _
      rw [Finset.sum, show (Finset.range (n + 1)).val = ↑(List.range (n + 1)) from rfl,
        Multiset.map_coe, Multiset.sum_coe]
    rw [h1, Finset.sum_flip, Nat.sum_range_multichoose, Nat.multichoose_eq,
      show k + 1 + n - 1 = n + k from by omega, Nat.choose_symm_add]

/-- Closed form for the cardinality of `Fin (n + 1) → ℕ` tuples summing to
`d`: it equals `(n + d) choose d`. -/
theorem Nat.card_antidiagonal_tuple_choose (n d : ℕ) :
    (Finset.Nat.antidiagonalTuple (n + 1) d).card = Nat.choose (n + d) d := by
  rw [card_antidiagonalTuple, Nat.multichoose_eq,
    show n + 1 + d - 1 = n + d from by omega]

/-- The growth (Hilbert) function of the polynomial ring `k[x_0, …, x_{d-1}]`
in degree `n`: `(n + d choose d)`. -/
def growthFun_polyring (d : ℕ) (n : ℕ) : ℕ := (n + d).choose d

/-- Auxiliary bound: `n^d ≤ (n + 1).ascFactorial d` for the growth function
analysis. -/
lemma pow_le_ascFactorial_succ' (n d : ℕ) : n ^ d ≤ (n + 1).ascFactorial d := by
  induction d with
  | zero => simp [Nat.ascFactorial]
  | succ d ih =>
    rw [pow_succ]
    calc n ^ d * n
        ≤ (n + 1).ascFactorial d * n := Nat.mul_le_mul_right n ih
      _ ≤ (n + 1).ascFactorial d * (n + 1 + d) := Nat.mul_le_mul_left _ (by omega)
      _ = (n + 1 + d) * (n + 1).ascFactorial d := by ring

/-- Lower bound on the polynomial growth function:
`n^d ≤ d! · growthFun_polyring d n`. -/
theorem growthFun_lower_bound (n d : ℕ) :
    n ^ d ≤ d.factorial * growthFun_polyring d n := by
  simp only [growthFun_polyring]
  calc n ^ d ≤ (n + 1).ascFactorial d := pow_le_ascFactorial_succ' n d
    _ = d.factorial * (n + d).choose d := Nat.ascFactorial_eq_factorial_mul_choose n d

/-- Upper bound on the polynomial growth function:
`growthFun_polyring d n ≤ 2^d · n^d` for `d ≤ n`. -/
theorem growthFun_upper_bound (n d : ℕ) (hnd : d ≤ n) :
    growthFun_polyring d n ≤ 2 ^ d * n ^ d := by
  simp only [growthFun_polyring]
  calc (n + d).choose d ≤ (n + d) ^ d := Nat.choose_le_pow _ _
    _ ≤ (2 * n) ^ d := by apply Nat.pow_le_pow_left; omega
    _ = 2 ^ d * n ^ d := by ring

/-- Filtration of a finitely-generated algebra by total-degree truncation:
the image under a presentation `f` of polynomials of total degree `≤ n`. -/
def generatorFiltration' {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : Submodule k A :=
  Submodule.map f.toLinearMap (MvPolynomial.restrictTotalDegree (Fin m) k n)

/-- Growth function of a finitely-generated algebra `A` along a presentation
`f`: the `k`-dimension of the degree-`n` filtration piece. -/
def growthFun {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : ℕ :=
  Module.finrank k (generatorFiltration' f n)

/-- Noether normalization growth comparison: the growth function of `A` is
sandwiched between the polynomial growth function `growthFun_polyring d` and
a uniform multiple of it. -/
theorem noether_normalization_growth_comparison'
    (k : Type*) [Field k]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (d : ℕ) (hd : ringKrullDim A = d)
    (m : ℕ) (f : MvPolynomial (Fin m) k →ₐ[k] A) (hf : Function.Surjective f) :
    ∃ C : ℕ, 0 < C ∧
      (∀ n, growthFun_polyring d n ≤ growthFun f n) ∧
      (∀ n, growthFun f n ≤ C * growthFun_polyring d n) := by sorry

/-- Proposition 11 (separatedness/growth criterion): for a finitely-generated
`k`-algebra `A` of Krull dimension `d`, the growth function satisfies
`n^d ≲ growthFun f n ≲ n^d`. -/
theorem proposition_11
    (k : Type*) [Field k]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (d : ℕ) (hd : ringKrullDim A = d)
    (m : ℕ) (f : MvPolynomial (Fin m) k →ₐ[k] A) (hf : Function.Surjective f) :
    ∃ (c' c : ℕ), 0 < c' ∧ 0 < c ∧
      (∀ n : ℕ, n ^ d ≤ c' * growthFun f n) ∧
      (∀ n : ℕ, d ≤ n → growthFun f n ≤ c * n ^ d) := by
  obtain ⟨C, hC_pos, hle, hup⟩ := noether_normalization_growth_comparison' k A d hd m f hf
  refine ⟨d.factorial, C * 2 ^ d, Nat.factorial_pos d, by positivity, ?_, ?_⟩
  · intro n
    calc n ^ d ≤ d.factorial * growthFun_polyring d n := growthFun_lower_bound n d
      _ ≤ d.factorial * growthFun f n := Nat.mul_le_mul_left _ (hle n)
  · intro n hnd
    calc growthFun f n ≤ C * growthFun_polyring d n := hup n
      _ ≤ C * (2 ^ d * n ^ d) :=
          Nat.mul_le_mul_left C (growthFun_upper_bound n d hnd)
      _ = (C * 2 ^ d) * n ^ d := by ring
