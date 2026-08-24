/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.EndAlgClassification

open scoped TensorProduct

namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The involution of a positive-definite involution algebra sends `0` to `0`. -/
theorem invol_zero : invol (0 : A) = 0 := by
  have h := invol_add (0 : A) (0 : A)
  rw [add_zero] at h
  have : invol (0 : A) + invol (0 : A) = invol (0 : A) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

end PositiveDefiniteInvolutionAlgebra

/-- The structure map `ℚ → A` of a nontrivial positive-definite involution algebra
is injective. Used to identify `ℚ` with its image inside `A`. -/
theorem PositiveDefiniteInvolutionAlgebra.algebraMap_injective
    {A : Type*} [Ring A] [Algebra ℚ A] [Nontrivial A] :
    Function.Injective (algebraMap ℚ A) := by
  intro x y hxy
  by_contra h
  have hne : x - y ≠ 0 := sub_ne_zero.mpr h
  have h0 : (algebraMap ℚ A) (x - y) = 0 := by rw [map_sub, sub_eq_zero.mpr hxy]
  have h1 : (x - y)⁻¹ • (algebraMap ℚ A) (x - y) = 0 := by rw [h0, smul_zero]
  rw [Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hne, one_smul] at h1
  exact one_ne_zero h1

namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The norm map of a nontrivial PD-involution algebra sends `0` to `0`. -/
theorem normMap_zero [Nontrivial A] : normMap (0 : A) = 0 := by
  have h := normMap_spec (0 : A)
  rw [zero_mul] at h
  have : (algebraMap ℚ A) (normMap (0 : A)) = (algebraMap ℚ A) 0 := by
    rw [h.symm, map_zero]
  exact algebraMap_injective this

/-- The norm of any element of a nontrivial PD-involution algebra is nonnegative. -/
theorem normMap_nonneg [Nontrivial A] (a : A) : 0 ≤ normMap a := by
  by_cases ha : a = 0
  · rw [ha, normMap_zero]
  · exact le_of_lt (normMap_pos a ha)

/-- The norm of an element vanishes iff the element itself is zero. Encodes
positive-definiteness of the norm form. -/
theorem normMap_eq_zero_iff [Nontrivial A] (a : A) : normMap a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    exact absurd h (ne_of_gt (normMap_pos a ha))
  · intro h
    rw [h, normMap_zero]

/-- A nontrivial PD-involution algebra has no zero divisors: if `a * b = 0`
then `a = 0` or `b = 0`. Proved using positive-definiteness of the norm. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero [Nontrivial A] (a b : A) (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  have hNb_ne : normMap b ≠ 0 := ne_of_gt (normMap_pos b hb)
  have h1 : a * (b * invol b) = 0 := by rw [← mul_assoc, hab, zero_mul]
  rw [normMap_spec b, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h1
  have h2 : a = (normMap b)⁻¹ • (normMap b • a) := by rw [inv_smul_smul₀ hNb_ne]
  rw [h1, smul_zero] at h2
  exact ha h2

/-- The norm is invariant under the involution: `N(â) = N(a)`. -/
theorem normMap_invol [Nontrivial A] (a : A) : normMap (invol a) = normMap a := by
  by_cases ha : a = 0
  · subst ha; simp only [invol_zero, normMap_zero]
  · have h1 : invol a * a = (algebraMap ℚ A) (normMap (invol a)) := by
      have := normMap_spec (invol a)
      rwa [invol_invol] at this
    have h2 : a * invol a = (algebraMap ℚ A) (normMap a) := normMap_spec a
    have h3 : a * (invol a * a) = (a * invol a) * a := (mul_assoc a (invol a) a).symm
    rw [h1, h2, Algebra.commutes] at h3
    have h4 : a * ((algebraMap ℚ A) (normMap (invol a)) - (algebraMap ℚ A) (normMap a)) = 0 := by
      rw [mul_sub, h3, sub_self]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero _ _ h4 with h5 | h5
    · exact absurd h5 ha
    · rw [← map_sub] at h5
      have := algebraMap_injective (show (algebraMap ℚ A) (normMap (invol a) - normMap a) =
        (algebraMap ℚ A) (0 : ℚ) from by rw [h5, map_zero])
      linarith

/-- Multiplicativity of the norm: `N(a * b) = N(a) * N(b)`. -/
theorem normMap_mul [Nontrivial A] (a b : A) :
    normMap (a * b) = normMap a * normMap b := by
  have h1 := normMap_spec (a * b)
  rw [invol_mul] at h1
  have h2 : a * b * (invol b * invol a) = a * (b * invol b) * invol a := by
    simp only [mul_assoc]
  rw [normMap_spec b] at h2
  have h3 : a * (algebraMap ℚ A) (normMap b) * invol a =
            (algebraMap ℚ A) (normMap b) * (a * invol a) := by
    rw [← Algebra.commutes (normMap b) a, mul_assoc]
  rw [normMap_spec a, ← map_mul] at h3
  rw [h2, h3] at h1
  have h4 := algebraMap_injective h1
  linarith

/-- Every nonzero element of a nontrivial PD-involution algebra is a unit. The
inverse is explicitly `N(a)⁻¹ • â`. -/
theorem isUnit_of_ne_zero [Nontrivial A] (a : A) (ha : a ≠ 0) : IsUnit a := by
  let Na := normMap a
  let ahat := invol a
  have hNa_pos : 0 < Na := normMap_pos a ha
  have hNa_ne : Na ≠ 0 := ne_of_gt hNa_pos
  let b := (Na⁻¹ : ℚ) • ahat
  have h_spec : a * ahat = (algebraMap ℚ A) Na := normMap_spec a
  have h_mul_right : a * b = 1 := by
    show a * ((Na⁻¹ : ℚ) • ahat) = 1
    rw [Algebra.mul_smul_comm, h_spec, Algebra.algebraMap_eq_smul_one,
        smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]
  have h_spec_invol : ahat * a = (algebraMap ℚ A) Na := by
    have := normMap_spec (invol a)
    rwa [invol_invol, normMap_invol] at this
  have h_mul_left : b * a = 1 := by
    show (Na⁻¹ : ℚ) • ahat * a = 1
    rw [Algebra.smul_mul_assoc, h_spec_invol, Algebra.algebraMap_eq_smul_one,
        smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]
  exact ⟨⟨a, b, h_mul_right, h_mul_left⟩, rfl⟩

/-- A nontrivial PD-involution algebra has no zero divisors. -/
instance instNoZeroDivisors [Nontrivial A] : NoZeroDivisors A where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := eq_zero_or_eq_zero_of_mul_eq_zero a b hab

/-- A nontrivial PD-involution algebra is an integral domain. -/
instance instIsDomain [Nontrivial A] : IsDomain A :=
  NoZeroDivisors.to_isDomain A

/-- Explicit two-sided inverse for a nonzero element `a`: `(N(a))⁻¹ • â` is both
a left and right inverse of `a`. -/
theorem inverse_eq [Nontrivial A] (a : A) (ha : a ≠ 0) :
    a * ((normMap a)⁻¹ • invol a) = 1 ∧
    ((normMap a)⁻¹ • invol a) * a = 1 := by
  have hNa_ne : normMap a ≠ 0 := ne_of_gt (normMap_pos a ha)
  constructor
  · rw [Algebra.mul_smul_comm, normMap_spec a, Algebra.algebraMap_eq_smul_one,
        smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]
  · have h : invol a * a = (algebraMap ℚ A) (normMap a) := by
      have := normMap_spec (invol a)
      rwa [invol_invol, normMap_invol] at this
    rw [Algebra.smul_mul_assoc, h, Algebra.algebraMap_eq_smul_one,
        smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]

end PositiveDefiniteInvolutionAlgebra

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)

/-- The rational endomorphism algebra `End⁰(E) = End(E) ⊗_ℤ ℚ` of an elliptic
curve `E`, an abbreviation for `EndomorphismAlgebra E`. -/
abbrev End0 := EndomorphismAlgebra E

/-- The Rosati dual / canonical involution of an element of `End⁰(E)`,
obtained from the PD-involution algebra structure on the endomorphism algebra. -/
noncomputable def End0.dual (α : End0 E) : End0 E :=
  @PositiveDefiniteInvolutionAlgebra.invol (End0 E)
    (EndomorphismAlgebra.instRing E) (EndomorphismAlgebra.instAlgebra E)
    (EndomorphismAlgebra.instPDInvAlgebra E) α

/-- The reduced norm `N : End⁰(E) → ℚ` of an endomorphism, obtained from the
PD-involution algebra structure on `End⁰(E)`. Geometrically this is the
degree of an isogeny (extended ℚ-linearly). -/
noncomputable def End0.N (α : End0 E) : ℚ :=
  @PositiveDefiniteInvolutionAlgebra.normMap (End0 E)
    (EndomorphismAlgebra.instRing E) (EndomorphismAlgebra.instAlgebra E)
    (EndomorphismAlgebra.instPDInvAlgebra E) α

/-- Defining property of the norm: `N(α) = α · α^†` after embedding ℚ into
`End⁰(E)`. -/
theorem End0.N_spec (α : End0 E) :
    letI := EndomorphismAlgebra.instRing E
    letI := EndomorphismAlgebra.instAlgebra E
    (algebraMap ℚ (End0 E)) (End0.N E α) = α * End0.dual E α := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  exact (PositiveDefiniteInvolutionAlgebra.normMap_spec α).symm

/-- The endomorphism algebra `End⁰(E)` is nontrivial (contains both `0` and `1`). -/
noncomputable instance End0.instNontrivial :
    letI := EndomorphismAlgebra.instRing E; Nontrivial (End0 E) :=
  letI := EndomorphismAlgebra.instRing E
  _root_.WeierstrassCurve.Affine.EndomorphismAlgebra.instNontrivial E

/-- Nonnegativity of the endomorphism norm: `N(α) ≥ 0` for all `α ∈ End⁰(E)`. -/
theorem EndAlgebra.norm_nonneg (α : End0 E) : 0 ≤ End0.N E α := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_nonneg α

/-- Positive-definiteness of the norm: `N(α) = 0` iff `α = 0`. -/
theorem EndAlgebra.norm_eq_zero_iff (α : End0 E) : End0.N E α = 0 ↔ α = 0 := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_eq_zero_iff α

/-- The norm is invariant under the Rosati dual: `N(α^†) = N(α)`. -/
theorem EndAlgebra.norm_dual (α : End0 E) : End0.N E (End0.dual E α) = End0.N E α := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_invol α

/-- Multiplicativity of the norm on `End⁰(E)`: `N(α · β) = N(α) · N(β)`. -/
theorem EndAlgebra.norm_mul (α β : End0 E) :
    End0.N E (α * β) = End0.N E α * End0.N E β := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_mul α β

/-- Bundled statement of the main norm properties on `End⁰(E)`:
nonnegativity, positive-definiteness, invariance under dual, multiplicativity. -/
theorem EndAlgebra.norm_properties (α β : End0 E) :
    0 ≤ End0.N E α ∧
    (End0.N E α = 0 ↔ α = 0) ∧
    End0.N E (End0.dual E α) = End0.N E α ∧
    End0.N E (α * β) = End0.N E α * End0.N E β :=
  ⟨EndAlgebra.norm_nonneg E α, EndAlgebra.norm_eq_zero_iff E α,
   EndAlgebra.norm_dual E α, EndAlgebra.norm_mul E α β⟩

/-- Every nonzero element of `End⁰(E)` is invertible, making `End⁰(E)` a
division algebra over `ℚ`. -/
theorem EndAlgebra.isUnit_of_ne_zero (a : End0 E) (ha : a ≠ 0) : IsUnit a := by
  letI : Ring (End0 E) := EndomorphismAlgebra.instRing E
  letI : Algebra ℚ (End0 E) := EndomorphismAlgebra.instAlgebra E
  letI : PositiveDefiniteInvolutionAlgebra (End0 E) := EndomorphismAlgebra.instPDInvAlgebra E
  letI : Nontrivial (End0 E) := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.isUnit_of_ne_zero a ha

/-- The reduced trace `T : End⁰(E) → ℚ` of an endomorphism, obtained from the
PD-involution structure on `End⁰(E)`. -/
noncomputable def End0.T (α : End0 E) : ℚ :=
  @PositiveDefiniteInvolutionAlgebra.traceMap (End0 E)
    (EndomorphismAlgebra.instRing E) (EndomorphismAlgebra.instAlgebra E)
    (EndomorphismAlgebra.instPDInvAlgebra E) α

end WeierstrassCurve.Affine

namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- Defining property of the trace map: `T(a)` mapped into `A` equals `a + â`. -/
theorem traceMap_spec [Nontrivial A] (a : A) :
    (algebraMap ℚ A) (traceMap a) = a + invol a := by
  unfold traceMap
  have h1 := normMap_spec (a + 1)
  have h2 := normMap_spec a
  rw [invol_add, invol_one] at h1

  have expand : (a + 1) * (invol a + 1) = a * invol a + a + invol a + 1 := by
    rw [add_mul, mul_add, mul_add, mul_one, one_mul, one_mul]
    abel
  rw [expand, h2] at h1

  rw [map_sub, map_sub, map_one]


  have h3 : (algebraMap ℚ A) (normMap (a + 1)) =
      (algebraMap ℚ A) (normMap a) + (a + invol a) + 1 := by
    rw [← h1]; abel
  rw [h3]; abel

/-- The involution is ℚ-linear in the scalar action: `(r • a)^† = r • a^†`. -/
theorem invol_smul (r : ℚ) (a : A) :
    invol (r • a) = r • invol a := by
  rw [Algebra.smul_def, Algebra.smul_def, invol_mul, invol_rat]
  exact (Algebra.commutes r (invol a)).symm

/-- The trace is invariant under the involution: `T(â) = T(a)`. -/
theorem traceMap_invol [Nontrivial A] (a : A) : traceMap (invol a) = traceMap a := by
  apply algebraMap_injective (A := A)
  rw [traceMap_spec, traceMap_spec, invol_invol, add_comm]

/-- Additivity of the trace: `T(a + b) = T(a) + T(b)`. -/
theorem traceMap_add [Nontrivial A] (a b : A) :
    traceMap (a + b) = traceMap a + traceMap b := by
  apply algebraMap_injective (A := A)
  rw [map_add, traceMap_spec, traceMap_spec, traceMap_spec, invol_add]
  abel

/-- ℚ-linearity of the trace: `T(r • a) = r * T(a)`. -/
theorem traceMap_smul [Nontrivial A] (r : ℚ) (a : A) :
    traceMap (r • a) = r * traceMap a := by
  apply algebraMap_injective (A := A)
  rw [map_mul, traceMap_spec, traceMap_spec, invol_smul]
  rw [Algebra.smul_def, Algebra.smul_def, ← mul_add]

/-- Characteristic polynomial relation: every element satisfies
`a² - T(a) • a + N(a) • 1 = 0`. -/
theorem char_poly [Nontrivial A] (a : A) :
    a ^ 2 - (traceMap a) • a + (normMap a) • (1 : A) = 0 := by
  have hT := traceMap_spec a
  have hN := normMap_spec a
  rw [sq, Algebra.smul_def (traceMap a) a, Algebra.smul_def (normMap a) (1 : A), mul_one]
  rw [Algebra.commutes (traceMap a) a]
  rw [hT, mul_add, ← hN]
  abel

/-- The trace of `algebraMap q` is `2q`, matching the formula `T(q · 1) = 2q`
for the reduced trace of a scalar. -/
theorem traceMap_algebraMap [Nontrivial A] (q : ℚ) :
    traceMap ((algebraMap ℚ A) q) = 2 * q := by
  apply algebraMap_injective (A := A)
  rw [traceMap_spec, invol_rat, ← two_mul, map_mul, map_ofNat]

/-- The trace of `â · a` is strictly positive for any nonzero `a`, since
`â · a = N(a) · 1` and `T(N(a) · 1) = 2 N(a) > 0`. -/
theorem traceMap_invol_mul_self_pos [Nontrivial A] (a : A) (ha : a ≠ 0) :
    0 < traceMap (invol a * a) := by
  have h_spec : invol a * a = (algebraMap ℚ A) (normMap (invol a)) := by
    have := normMap_spec (invol a)
    rwa [invol_invol] at this
  have h_eq : normMap (invol a) = normMap a := normMap_invol a
  rw [show invol a * a = (algebraMap ℚ A) (normMap a) from by rw [h_spec, h_eq]]
  rw [traceMap_algebraMap]
  linarith [normMap_pos a ha]

end PositiveDefiniteInvolutionAlgebra

namespace WeierstrassCurve.Affine

universe u₂

variable {F : Type u₂} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)

/-- Rationality formula for the trace on `End⁰(E)`:
`T(α) = 1 + N(α) - N(1 - α)`, expressing the trace as a polynomial in norms. -/
theorem EndAlgebra.trace_rationality (α : End0 E) :
    End0.T E α = 1 + End0.N E α - End0.N E (1 - α) := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E


  show PositiveDefiniteInvolutionAlgebra.traceMap α =
    1 + PositiveDefiniteInvolutionAlgebra.normMap α -
    PositiveDefiniteInvolutionAlgebra.normMap (1 - α)

  apply PositiveDefiniteInvolutionAlgebra.algebraMap_injective (A := End0 E)
  rw [PositiveDefiniteInvolutionAlgebra.traceMap_spec]
  rw [map_sub, map_add, map_one]

  have hN := PositiveDefiniteInvolutionAlgebra.normMap_spec α
  have hN1 := PositiveDefiniteInvolutionAlgebra.normMap_spec (1 - α)

  have hsub : (1 : End0 E) - α = 1 + (-α) := sub_eq_add_neg 1 α
  have hinv_neg : PositiveDefiniteInvolutionAlgebra.invol (-α) =
      -PositiveDefiniteInvolutionAlgebra.invol α := by
    have h0 := PositiveDefiniteInvolutionAlgebra.invol_zero (A := End0 E)
    have := PositiveDefiniteInvolutionAlgebra.invol_add α (-α)
    rw [add_neg_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hinv_sub : PositiveDefiniteInvolutionAlgebra.invol (1 - α) =
      1 - PositiveDefiniteInvolutionAlgebra.invol α := by
    rw [hsub, PositiveDefiniteInvolutionAlgebra.invol_add,
        PositiveDefiniteInvolutionAlgebra.invol_one, hinv_neg, sub_eq_add_neg]
  rw [hinv_sub] at hN1
  have expand : (1 - α) * (1 - PositiveDefiniteInvolutionAlgebra.invol α) =
      1 - α - PositiveDefiniteInvolutionAlgebra.invol α +
      α * PositiveDefiniteInvolutionAlgebra.invol α := by noncomm_ring
  rw [expand, hN] at hN1


  rw [← hN1]; abel

/-- The trace is invariant under the Rosati dual: `T(α^†) = T(α)`. -/
theorem EndAlgebra.trace_dual (α : End0 E) : End0.T E (End0.dual E α) = End0.T E α := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.traceMap_invol α

/-- Additivity of the trace on `End⁰(E)`: `T(α + β) = T(α) + T(β)`. -/
theorem EndAlgebra.trace_add (α β : End0 E) :
    End0.T E (α + β) = End0.T E α + End0.T E β := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.traceMap_add α β

/-- ℚ-linearity of the trace on `End⁰(E)`: `T(r • α) = r · T(α)`. -/
theorem EndAlgebra.trace_smul (r : ℚ) (α : End0 E) :
    End0.T E (r • α) = r * End0.T E α := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.traceMap_smul r α

/-- Bundled package: the trace on `End⁰(E)` is dual-invariant, ℚ-rational via
`T(α) = 1 + N(α) - N(1 - α)`, additive, and ℚ-linear in the scalar action. -/
theorem EndAlgebra.trace_dual_and_linear :
    (∀ α : End0 E, End0.T E (End0.dual E α) = End0.T E α) ∧
    (∀ α : End0 E, End0.T E α = 1 + End0.N E α - End0.N E (1 - α)) ∧
    (∀ α β : End0 E, End0.T E (α + β) = End0.T E α + End0.T E β) ∧
    (∀ (r : ℚ) (α : End0 E), End0.T E (r • α) = r * End0.T E α) :=
  ⟨EndAlgebra.trace_dual E, EndAlgebra.trace_rationality E,
   EndAlgebra.trace_add E, EndAlgebra.trace_smul E⟩

/-- Every endomorphism `α` satisfies its characteristic equation in `End⁰(E)`:
`α² - T(α) • α + N(α) • 1 = 0`. -/
theorem EndAlgebra.char_poly (α : End0 E) :
    α ^ 2 - (End0.T E α) • α + (End0.N E α) • (1 : End0 E) = 0 := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.char_poly α

/-- The dual `α^†` also satisfies `α`'s characteristic polynomial:
`(α^†)² - T(α) • α^† + N(α) • 1 = 0`. -/
theorem EndAlgebra.char_poly_dual (α : End0 E) :
    End0.dual E α ^ 2 - (End0.T E α) • End0.dual E α + (End0.N E α) • (1 : End0 E) = 0 := by
  rw [← EndAlgebra.trace_dual E α, ← EndAlgebra.norm_dual E α]
  exact EndAlgebra.char_poly E (End0.dual E α)

/-- The characteristic polynomial of an endomorphism `α`, as the polynomial
`X² - T(α) X + N(α) ∈ ℚ[X]`. -/
noncomputable def End0.charPolyOf (α : End0 E) : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C (End0.T E α) * Polynomial.X + Polynomial.C (End0.N E α)

/-- `α` is a root of its own characteristic polynomial under the ℚ-algebra
evaluation `Polynomial ℚ → End⁰(E)`. -/
theorem EndAlgebra.alpha_is_root_of_char_poly (α : End0 E) :
    letI := EndomorphismAlgebra.instRing E
    letI := EndomorphismAlgebra.instAlgebra E
    (Polynomial.aeval α) (End0.charPolyOf E α) = 0 := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  simp only [End0.charPolyOf, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C]
  rw [show (algebraMap ℚ (End0 E)) (End0.T E α) * α = (End0.T E α) • α from
    (Algebra.smul_def (End0.T E α) α).symm]
  rw [show (algebraMap ℚ (End0 E)) (End0.N E α) = (End0.N E α) • (1 : End0 E) from by
    rw [Algebra.smul_def, mul_one]]
  exact EndAlgebra.char_poly E α

/-- The Rosati dual `α^†` is also a root of `α`'s characteristic polynomial. -/
theorem EndAlgebra.dual_is_root_of_char_poly (α : End0 E) :
    letI := EndomorphismAlgebra.instRing E
    letI := EndomorphismAlgebra.instAlgebra E
    (Polynomial.aeval (End0.dual E α)) (End0.charPolyOf E α) = 0 := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  simp only [End0.charPolyOf, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C]
  rw [show (algebraMap ℚ (End0 E)) (End0.T E α) * End0.dual E α = (End0.T E α) • End0.dual E α from
    (Algebra.smul_def (End0.T E α) (End0.dual E α)).symm]
  rw [show (algebraMap ℚ (End0 E)) (End0.N E α) = (End0.N E α) • (1 : End0 E) from by
    rw [Algebra.smul_def, mul_one]]
  exact EndAlgebra.char_poly_dual E α

/-- Both `α` and its Rosati dual `α^†` are roots of the characteristic polynomial
`X² - T(α) X + N(α)`. -/
theorem EndAlgebra.roots_of_char_poly (α : End0 E) :
    letI := EndomorphismAlgebra.instRing E
    letI := EndomorphismAlgebra.instAlgebra E
    (Polynomial.aeval α) (End0.charPolyOf E α) = 0 ∧
    (Polynomial.aeval (End0.dual E α)) (End0.charPolyOf E α) = 0 :=
  ⟨EndAlgebra.alpha_is_root_of_char_poly E α, EndAlgebra.dual_is_root_of_char_poly E α⟩

/-- The Rosati-fixed elements of `End⁰(E)` are exactly the rational multiples of
the identity: `α^† = α` iff `α = r • 1` for some `r ∈ ℚ`. -/
theorem EndAlgebra.rosati_fixed_iff_rational (α : End0 E) :
    End0.dual E α = α ↔ ∃ r : ℚ, α = r • 1 := by
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  constructor
  ·
    intro h
    have hinv : PositiveDefiniteInvolutionAlgebra.invol α = α := h
    have hT := PositiveDefiniteInvolutionAlgebra.traceMap_spec α
    rw [hinv] at hT
    have h2 : (algebraMap ℚ (End0 E)) (PositiveDefiniteInvolutionAlgebra.traceMap α) = (2 : ℚ) • α := by
      rw [hT, two_smul]
    rw [Algebra.algebraMap_eq_smul_one] at h2
    refine ⟨PositiveDefiniteInvolutionAlgebra.traceMap α / 2, ?_⟩
    have h3 : (2 : ℚ) ≠ 0 := two_ne_zero
    calc α = (2 : ℚ)⁻¹ • ((2 : ℚ) • α) := by rw [inv_smul_smul₀ h3]
      _ = (2 : ℚ)⁻¹ • (PositiveDefiniteInvolutionAlgebra.traceMap α • (1 : End0 E)) := by rw [h2]
      _ = ((2 : ℚ)⁻¹ * PositiveDefiniteInvolutionAlgebra.traceMap α) • (1 : End0 E) := by rw [smul_smul]
      _ = (PositiveDefiniteInvolutionAlgebra.traceMap α / 2) • (1 : End0 E) := by rw [inv_mul_eq_div]
  ·
    rintro ⟨r, rfl⟩
    show PositiveDefiniteInvolutionAlgebra.invol (r • (1 : End0 E)) = r • 1
    rw [PositiveDefiniteInvolutionAlgebra.invol_smul,
        PositiveDefiniteInvolutionAlgebra.invol_one]

end WeierstrassCurve.Affine
