/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SobolevEmbedding
import Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz

open MeasureTheory Filter Topology
open scoped ZeroAtInfty

noncomputable section

namespace SchwartzWeightedSobolev

/-- The `k`-th weighted Sobolev space on `ℝⁿ`: a structure recording an
underlying Sobolev representative, used to model functions `f` such that
`⟨x⟩^k · f ∈ H^k`. -/
structure WeightedSobolevSpace (n : ℕ) (k : ℕ) where
  witness : SobolevEmbedding.SobolevSpace n k

/-- The underlying function of a `WeightedSobolevSpace n k` element: divide
the Sobolev witness by `⟨x⟩^k` so that the witness's `Hᵏ` regularity
translates into pointwise `⟨x⟩^k`-decay of the original function. -/
def WeightedSobolevSpace.toFun {n k : ℕ} (u : WeightedSobolevSpace n k)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (↑(TestFunctions.japaneseBracket n x ^ k))⁻¹ * u.witness.toFun x

/-- Coercion that lets an element of `WeightedSobolevSpace n k` be applied as
a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
instance {n k : ℕ} : CoeFun (WeightedSobolevSpace n k)
    (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨WeightedSobolevSpace.toFun⟩

/-- Bundle of a function lying in every weighted Sobolev space, with a
consistent family of weighted Sobolev witnesses. -/
structure MemAllWeightedSobolev (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  mem_weighted (k : ℕ) : WeightedSobolevSpace n k
  consistent (k : ℕ) :
    ∀ x, toFun x = WeightedSobolevSpace.toFun (mem_weighted k) x

/-- Coercion that lets an element of `MemAllWeightedSobolev n` be applied as
a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
instance {n : ℕ} : CoeFun (MemAllWeightedSobolev n)
    (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨MemAllWeightedSobolev.toFun⟩


/-- The iterated Fréchet derivatives (up to order `k`) of the `Cᵏ` witness of
a Schwartz test function lie in `L²` with respect to Lebesgue measure. -/
theorem schwartz_ck_iteratedFDeriv_memLp {n : ℕ}
    (u : TestFunctions.SchwartzTestFunctionSpace n) (k j : ℕ) (hj : j ≤ k) :
    MeasureTheory.MemLp
      (fun x => iteratedFDeriv ℝ j
        (fun x => (u.mem_weightedSpace k k).choose.witnessV.toZeroAtInftyContinuousMap x) x)
      2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by sorry

/-- From a Schwartz test function `u`, extract a `Hᵏ` Sobolev representative
(for every `k`) by taking the weighted `Cᵏ`-witness's underlying function. -/
def schwartzToSobolev {n : ℕ}
    (u : TestFunctions.SchwartzTestFunctionSpace n) (k : ℕ) :
    { s : SobolevEmbedding.SobolevSpace n k //
      s.toFun = fun x => (u.mem_weightedSpace k k).choose.witnessV.toZeroAtInftyContinuousMap x } :=
  ⟨⟨fun x => (u.mem_weightedSpace k k).choose.witnessV.toZeroAtInftyContinuousMap x,
    (u.mem_weightedSpace k k).choose.witnessV.contDiff_k,
    fun j hj => schwartz_ck_iteratedFDeriv_memLp u k j hj⟩, rfl⟩

/-- A Schwartz test function lies in every weighted Sobolev space, with
underlying function equal to the original Schwartz function. -/
def schwartzToAllWeightedSobolev {n : ℕ}
    (u : TestFunctions.SchwartzTestFunctionSpace n) :
    { w : MemAllWeightedSobolev n // w.toFun = u.toFun } := by


  refine ⟨⟨u.toFun, fun k => ⟨(schwartzToSobolev u k).val⟩, fun k x => ?_⟩, rfl⟩


  simp only [WeightedSobolevSpace.toFun, schwartzToSobolev]


  have hconsist := (u.mem_weightedSpace k k).choose_spec x
  rw [hconsist]

  simp only [TestFunctions.WeightedContDiffZeroAtInfty.toFun]

/-- Plain version of `schwartzToAllWeightedSobolev` discarding the proof of
the pointwise consistency identity. -/
def schwartzToAllWeightedSobolev' {n : ℕ}
    (u : TestFunctions.SchwartzTestFunctionSpace n) :
    MemAllWeightedSobolev n :=
  (schwartzToAllWeightedSobolev u).val

/-- Converse direction: a function lying in every weighted Sobolev space is a
Schwartz test function (and has the same underlying function). -/
@[simp]

def allWeightedSobolevToSchwartz {n : ℕ}
    (w : MemAllWeightedSobolev n) :
    { u : TestFunctions.SchwartzTestFunctionSpace n // u.toFun = w.toFun } := by


  have hf : ∀ k : ℕ, ∃ u : SobolevEmbedding.SobolevSpace n k,
      u.toFun = fun x =>
        (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) * w.toFun x := by
    intro k
    refine ⟨(w.mem_weighted k).witness, ?_⟩
    funext x
    have hcons := w.consistent k x


    have hne : (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) ≠ 0 :=
      SobolevEmbedding.japaneseBracket_pow_ne_zero_complex x k
    simp only [WeightedSobolevSpace.toFun] at hcons
    field_simp at hcons ⊢
    exact hcons.symm

  refine ⟨⟨w.toFun, fun j l => ?_⟩, rfl⟩

  let ⟨v, hv⟩ := SobolevEmbedding.weightedSobolev_to_contDiffZeroAtInfty w.toFun hf j l
  refine ⟨⟨v⟩, fun x => ?_⟩

  change w.toFun x = (↑(TestFunctions.japaneseBracket n x ^ l) : ℂ)⁻¹ *
    v.toZeroAtInftyContinuousMap x
  have hv_x : v.toZeroAtInftyContinuousMap x =
    (↑(TestFunctions.japaneseBracket n x ^ l) : ℂ) * w.toFun x := congr_fun hv x
  rw [hv_x]
  rw [inv_mul_cancel_left₀ (SobolevEmbedding.japaneseBracket_pow_ne_zero_complex x l)]

/-- Plain version of `allWeightedSobolevToSchwartz` discarding the proof of
the pointwise identity. -/
def allWeightedSobolevToSchwartz' {n : ℕ}
    (w : MemAllWeightedSobolev n) :
    TestFunctions.SchwartzTestFunctionSpace n :=
  (allWeightedSobolevToSchwartz w).val

/-- A function `f : ℝⁿ → ℂ` is Schwartz if it arises as the underlying
function of some element of `SchwartzTestFunctionSpace n`. -/
@[simp]

def IsSchwartz (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∃ u : TestFunctions.SchwartzTestFunctionSpace n, u.toFun = f

/-- A function `f : ℝⁿ → ℂ` lies in every weighted Sobolev space if it arises
as the underlying function of some `MemAllWeightedSobolev n`. -/
def IsInAllWeightedSobolev (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∃ w : MemAllWeightedSobolev n, w.toFun = f

end SchwartzWeightedSobolev
