/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Topology.KrullDimension

open TopologicalSpace Order

/-- A preorder is catenary when any two unrefinable (covering) chains with the same endpoints
have the same length. -/
def IsCatenary (α : Type*) [Preorder α] : Prop :=
  ∀ (s₁ s₂ : LTSeries α),
    s₁.toFun 0 = s₂.toFun 0 →
    s₁.toFun (Fin.last s₁.length) = s₂.toFun (Fin.last s₂.length) →
    (∀ i : Fin s₁.length, s₁.toFun i.castSucc ⋖ s₁.toFun i.succ) →
    (∀ i : Fin s₂.length, s₂.toFun i.castSucc ⋖ s₂.toFun i.succ) →
    s₁.length = s₂.length

/-- A commutative ring is catenary when its prime spectrum is catenary as a preorder. -/
def IsRingCatenary (R : Type*) [CommRing R] : Prop :=
  IsCatenary (PrimeSpectrum R)

/-- Any finitely generated `k`-algebra (in particular, any coordinate ring of an algebraic
variety) has a catenary prime spectrum (Prop 10, Lec 8). -/
theorem algebraicVariety_isCatenary (k : Type*) [Field k]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] :
    IsCatenary (PrimeSpectrum R) := by sorry

/-- A finitely generated `k`-algebra is a catenary ring. -/
theorem finiteType_isRingCatenary (k : Type*) [Field k]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] :
    IsRingCatenary R :=
  algebraicVariety_isCatenary k R

/-- The multivariate polynomial ring `k[x₁, …, xₙ]` is a catenary ring. -/
theorem MvPolynomial_isRingCatenary (k : Type*) [Field k] (n : ℕ) :
    IsRingCatenary (MvPolynomial (Fin n) k) :=
  finiteType_isRingCatenary k (MvPolynomial (Fin n) k)

/-- The univariate polynomial ring `k[x]` is a catenary ring. -/
theorem Polynomial_isRingCatenary (k : Type*) [Field k] :
    IsRingCatenary (Polynomial k) :=
  finiteType_isRingCatenary k (Polynomial k)

/-- In an unrefinable chain of closed irreducibles `X = Zₙ ⊋ … ⊋ Z₀` on an algebraic variety,
each `Z_i` has dimension `i` (Prop 10, Lec 8). -/
theorem algebraicVariety_catenary_chain
    (k : Type*) [Field k] (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R]
    {n : ℕ} (Z : Fin (n + 1) → IrreducibleCloseds (PrimeSpectrum R))
    (hcov : ∀ i : Fin n, Z i.castSucc ⋖ Z i.succ)
    (hmin : IsMin (Z 0))
    (hmax : IsMax (Z (Fin.last n))) :
    ∀ i : Fin (n + 1), topologicalKrullDim ↥(Z i) = ((i : ℕ) : WithBot ℕ∞) := by sorry

/-- The bottom element `Z₀` of an unrefinable chain of closed irreducibles is zero-dimensional. -/
theorem catenary_chain_dim_zero
    (k : Type*) [Field k] (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R]
    {n : ℕ} (Z : Fin (n + 1) → IrreducibleCloseds (PrimeSpectrum R))
    (hcov : ∀ i : Fin n, Z i.castSucc ⋖ Z i.succ)
    (hmin : IsMin (Z 0))
    (hmax : IsMax (Z (Fin.last n))) :
    topologicalKrullDim ↥(Z 0) = 0 := by
  have h := algebraicVariety_catenary_chain k R Z hcov hmin hmax 0
  simp only [Fin.val_zero, Nat.cast_zero] at h
  exact h

/-- The top element `Zₙ` of an unrefinable chain of closed irreducibles has dimension `n`. -/
theorem catenary_chain_dim_top
    (k : Type*) [Field k] (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R]
    {n : ℕ} (Z : Fin (n + 1) → IrreducibleCloseds (PrimeSpectrum R))
    (hcov : ∀ i : Fin n, Z i.castSucc ⋖ Z i.succ)
    (hmin : IsMin (Z 0))
    (hmax : IsMax (Z (Fin.last n))) :
    topologicalKrullDim ↥(Z (Fin.last n)) = ((n : ℕ) : WithBot ℕ∞) := by
  have h := algebraicVariety_catenary_chain k R Z hcov hmin hmax (Fin.last n)
  simp only [Fin.val_last] at h
  exact h

/-- Each step in an unrefinable chain of closed irreducibles increments the dimension by one. -/
theorem catenary_chain_dim_step
    (k : Type*) [Field k] (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R]
    {n : ℕ} (Z : Fin (n + 1) → IrreducibleCloseds (PrimeSpectrum R))
    (hcov : ∀ i : Fin n, Z i.castSucc ⋖ Z i.succ)
    (hmin : IsMin (Z 0))
    (hmax : IsMax (Z (Fin.last n)))
    (i : Fin n) :
    topologicalKrullDim ↥(Z i.succ) = topologicalKrullDim ↥(Z i.castSucc) + 1 := by
  have h1 := algebraicVariety_catenary_chain k R Z hcov hmin hmax i.succ
  have h2 := algebraicVariety_catenary_chain k R Z hcov hmin hmax i.castSucc
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at h1
  simp only [Fin.val_castSucc] at h2
  rw [h1, h2]
