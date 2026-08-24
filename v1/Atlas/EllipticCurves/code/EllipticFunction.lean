/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Lattice
import Atlas.EllipticCurves.code.ComplexAnalysis
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order

open Complex

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- If `f : ℂ → ℂ` is periodic with period `ω`, then it is periodic with period
`n * ω` for every integer `n`. Inductive consequence of additive periodicity. -/
lemma periodic_int_mul {f : ℂ → ℂ} {ω : ℂ} (h : ∀ w, f (w + ω) = f w)
    (n : ℤ) (w : ℂ) : f (w + ↑n * ω) = f w := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    suffices f ((w + (↑↑k : ℂ) * ω) + ω) = f w by
      convert this using 2; push_cast; ring
    rw [h]; exact ih
  | pred k ih =>
    suffices f ((w + (↑(-↑k : ℤ) : ℂ) * ω) - ω) = f w by
      convert this using 2; push_cast; ring
    have hminus : ∀ u, f (u - ω) = f u := fun u => by
      have := (h (u - ω)).symm; rwa [sub_add_cancel] at this
    rw [hminus]; exact ih

/-- A function `f : ℂ → ℂ` is `L`-periodic if `f(z + ω) = f(z)` for every `z ∈ ℂ` and
every lattice element `ω ∈ L`. -/
def IsLatticePeriodic (f : ℂ → ℂ) : Prop :=
  ∀ ω ∈ L.lattice, ∀ z : ℂ, f (z + ω) = f z

/-- Definition 14.8: an elliptic function for `L` is a meromorphic function on `ℂ`
that is `L`-periodic. -/
structure IsEllipticFunction (f : ℂ → ℂ) : Prop where
  meromorphic : Meromorphic f
  periodic : L.IsLatticePeriodic f

variable {L}

/-- Constant functions are `L`-periodic for any lattice `L`. -/
theorem isLatticePeriodic_const (c : ℂ) : L.IsLatticePeriodic (fun _ => c) :=
  fun _ _ _ => rfl

/-- The order of a pole of `f` at `z`: `n` if `f` has a pole of order `n` at `z`,
and `0` if `f` is holomorphic or has a zero at `z`. Extracted from
`meromorphicOrderAt` by negating and clamping to `ℕ`. -/
def poleMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  match meromorphicOrderAt f z with
  | ⊤ => 0
  | (n : ℤ) => (-n).toNat

/-- `f` has a pole at `z` iff its meromorphic order is strictly negative. -/
def IsPoleAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  meromorphicOrderAt f z < 0

variable (L) in
/-- The set of poles of `f` lying in the fundamental parallelogram with corner `α`. -/
def polesInFundParallelogram (f : ℂ → ℂ) (α : ℂ) : Set ℂ :=
  {z ∈ L.fundamentalParallelogram α | IsPoleAt f z}

/-- The poles of an elliptic function in any fundamental parallelogram form a finite
set, because they are a discrete subset of a bounded region (the closure of the
parallelogram is compact). -/
theorem polesInFundParallelogram_finite
    {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (α : ℂ) :
    Set.Finite (L.polesInFundParallelogram f α) := by
  open Topology Filter in
  by_contra h_inf
  have h_inf' : Set.Infinite (L.polesInFundParallelogram f α) := h_inf

  have h_bdd : Bornology.IsBounded (L.fundamentalParallelogram α) := by
    rw [Metric.isBounded_iff_subset_closedBall α]
    refine ⟨‖L.ω₁‖ + ‖L.ω₂‖, ?_⟩
    intro z hz
    rw [L.mem_fundamentalParallelogram_iff] at hz
    obtain ⟨t₁, t₂, ht₁_nn, ht₁_lt, ht₂_nn, ht₂_lt, rfl⟩ := hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : α + t₁ • L.ω₁ + t₂ • L.ω₂ - α = t₁ • L.ω₁ + t₂ • L.ω₂ := by abel
    rw [hsub]
    have h1 : ‖t₁ • L.ω₁‖ ≤ ‖L.ω₁‖ :=
      calc ‖t₁ • L.ω₁‖ ≤ ‖t₁‖ * ‖L.ω₁‖ := norm_smul_le t₁ L.ω₁
        _ ≤ 1 * ‖L.ω₁‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = ‖L.ω₁‖ := one_mul _
    have h2 : ‖t₂ • L.ω₂‖ ≤ ‖L.ω₂‖ :=
      calc ‖t₂ • L.ω₂‖ ≤ ‖t₂‖ * ‖L.ω₂‖ := norm_smul_le t₂ L.ω₂
        _ ≤ 1 * ‖L.ω₂‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = ‖L.ω₂‖ := one_mul _
    calc ‖t₁ • L.ω₁ + t₂ • L.ω₂‖
        ≤ ‖t₁ • L.ω₁‖ + ‖t₂ • L.ω₂‖ := norm_add_le _ _
      _ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := add_le_add h1 h2

  have h_compact := h_bdd.isCompact_closure

  have h_sub : L.polesInFundParallelogram f α ⊆ closure (L.fundamentalParallelogram α) := by
    intro z hz
    unfold polesInFundParallelogram at hz
    exact subset_closure (Set.mem_sep_iff.mp hz).1

  obtain ⟨x, -, hx_acc⟩ := h_inf'.exists_accPt_of_subset_isCompact h_compact h_sub

  have h_ev : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ f y := (hf.meromorphic x).eventually_analyticAt

  have h_disj : Disjoint (𝓝[≠] x) (𝓟 (L.polesInFundParallelogram f α)) := by
    rw [disjoint_principal_right]
    apply Filter.mem_of_superset h_ev
    intro y hy hy_mem
    unfold polesInFundParallelogram IsPoleAt at hy_mem
    exact absurd (Set.mem_sep_iff.mp hy_mem).2 (not_lt.mpr hy.meromorphicOrderAt_nonneg)

  exact hx_acc.ne (disjoint_iff.mp h_disj)

variable (L) in
/-- Definition 14.9: the order of an elliptic function `f` for `L`, computed as the
sum of pole multiplicities in the fundamental parallelogram with corner `0`. -/
def ellipticOrder (f : ℂ → ℂ) (hf : L.IsEllipticFunction f) : ℕ :=
  (polesInFundParallelogram_finite hf 0).toFinset.sum (fun z => poleMultiplicity f z)

/-- The order of an elliptic function is independent of the choice of fundamental
parallelogram. -/
theorem ellipticOrder_independent
    {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (α : ℂ) :
    (polesInFundParallelogram_finite hf α).toFinset.sum (fun z => poleMultiplicity f z) =
    ellipticOrder L f hf := by sorry

variable (L)

/-- `f` is a nonzero elliptic function for `L` if it is elliptic and not identically
zero. -/
def IsNonzeroElliptic (f : ℂ → ℂ) : Prop :=
  L.IsEllipticFunction f ∧ ∃ z : ℂ, f z ≠ 0

/-- The set of points in the fundamental parallelogram with corner `α` where `f` has
a nonzero `ord` (i.e., a zero or a pole). -/
def zerosAndPolesInFundParallelogram (f : ℂ → ℂ) (α : ℂ) : Set ℂ :=
  {z ∈ L.fundamentalParallelogram α | _root_.ord z f ≠ 0}

variable {L}

/-- The zeros and poles of a nonzero elliptic function in any fundamental parallelogram
form a finite set. -/
theorem zerosAndPolesInFundParallelogram_finite
    {f : ℂ → ℂ} (hf : L.IsNonzeroElliptic f) (α : ℂ) :
    Set.Finite (L.zerosAndPolesInFundParallelogram f α) := by sorry

/-- For a nonzero elliptic function `f`, the order `ord_z(f)` is finite (never `⊤`). -/
theorem ord_ne_top_of_nonzeroElliptic
    {f : ℂ → ℂ} (hf : L.IsNonzeroElliptic f) (z : ℂ) :
    _root_.ord z f ≠ ⊤ := by sorry

/-- The integer-valued order `ord_z(f) ∈ ℤ` for a nonzero elliptic function, extracted
by removing the `⊤` case. -/
def ordInt {f : ℂ → ℂ} (hf : L.IsNonzeroElliptic f) (z : ℂ) : ℤ :=
  (_root_.ord z f).untop (ord_ne_top_of_nonzeroElliptic hf z)

/-- For any nonzero elliptic function and any corner `α`, there exists a piecewise
smooth boundary curve `γ` of (a perturbation of) the fundamental parallelogram such
that `f` is meromorphic on an enclosing open set `Ω`, the zeros/poles of `f` lie in
the interior of `γ`, and the sum of `ord` values matches the sum along the boundary.
This packages the data needed to apply the argument principle. -/
theorem exists_fundParallelogram_boundary
    {f : ℂ → ℂ} (hf : L.IsNonzeroElliptic f) (α : ℂ) :
    ∃ (γ : PiecewiseSmoothCurve) (Ω : Set ℂ)
      (N : ℕ) (pts : Fin N → ℂ) (ords : Fin N → ℤ),
      IsOpen Ω ∧
      γ.IsClosed ∧
      γ.IsSimple ∧
      γ.IsPositivelyOriented ∧
      (∀ i : Fin γ.n, ∀ t ∈ Set.Icc (γ.pieces i).a (γ.pieces i).b,
        (γ.pieces i).toFun t ∈ Ω) ∧
      (γ.image ∪ γ.interiorRegion ⊆ Ω) ∧
      IsMeromorphicOn f Ω ∧
      (∀ k : Fin N, pts k ∈ γ.interiorRegion) ∧
      (∀ k : Fin N, _root_.ord (pts k) f = (ords k : WithTop ℤ)) ∧
      (∀ z ∈ Ω, (∀ k : Fin N, z ≠ pts k) → AnalyticAt ℂ f z ∧ f z ≠ 0) ∧
      (∀ i : Fin γ.n, ∀ t ∈ Set.Icc (γ.pieces i).a (γ.pieces i).b,
        AnalyticAt ℂ f ((γ.pieces i).toFun t) ∧ f ((γ.pieces i).toFun t) ≠ 0) ∧

      (zerosAndPolesInFundParallelogram_finite hf α).toFinset.sum (fun z => ordInt hf z) =
        ∑ k : Fin N, ords k := by sorry

/-- The contour integral of `f'/f` around the boundary `γ` of a fundamental
parallelogram vanishes, because periodic boundary identifications make opposite sides
cancel. -/
theorem contour_integral_f'_over_f_vanishes
    {f : ℂ → ℂ} (hf : L.IsNonzeroElliptic f)
    (γ : PiecewiseSmoothCurve) :
    γ.contourIntegral (fun z => deriv f z / f z) = 0 := by sorry

/-- Theorem 14.18: for any nonzero elliptic function `f`, the number of zeros equals
the number of poles in any fundamental parallelogram (counted with multiplicity).
Equivalently, the sum of `ord` over zeros and poles is zero. Proof combines the
argument principle (Theorem 14.17) with vanishing of the boundary contour integral. -/
theorem sum_ord_eq_zero_of_nonzeroElliptic
    {f : ℂ → ℂ} (hf : L.IsNonzeroElliptic f) (α : ℂ) :
    (zerosAndPolesInFundParallelogram_finite hf α).toFinset.sum
      (fun z => ordInt hf z) = 0 := by

  obtain ⟨γ, Ω, N, pts, ords, hΩ, hγ_closed, hγ_simple, hγ_pos, hγ_in_Ω,
    hinterior_in_Ω, hf_mero, hpts_in_interior, hord, hf_holo_off, hf_on_curve,
    hsum_match⟩ :=
    exists_fundParallelogram_boundary hf α


  have h_arg_principle := theorem_14_17 f (fun _ => (1 : ℂ)) γ Ω N pts ords
    hΩ hf_mero (fun _ hx => differentiableAt_const (1 : ℂ) |>.differentiableWithinAt)
    hγ_closed hγ_simple hγ_pos hγ_in_Ω hinterior_in_Ω hpts_in_interior hord
    hf_holo_off hf_on_curve

  have h_vanish := contour_integral_f'_over_f_vanishes hf γ

  simp only [one_mul] at h_arg_principle

  rw [h_vanish] at h_arg_principle

  have h2piI_ne : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact two_ne_zero
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  have h_sum_zero : (∑ k : Fin N, (ords k : ℂ)) = 0 :=
    (mul_eq_zero.mp h_arg_principle.symm).resolve_left h2piI_ne

  rw [hsum_match]
  exact_mod_cast h_sum_zero

end ComplexLattice

end
