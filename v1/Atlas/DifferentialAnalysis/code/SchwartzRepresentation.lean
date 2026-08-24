/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SobolevEmbedding
import Mathlib.Analysis.Distribution.TemperateGrowth

open scoped ZeroAtInfty SchwartzMap
open MeasureTheory Filter Topology SchwartzRepresentation

noncomputable section

namespace SchwartzRepresentation

variable {n : ℕ}

/-- A finite product of functions of temperate growth (in the sense of Schwartz) is again of
temperate growth, proved by induction on the finset using closure of `HasTemperateGrowth`
under multiplication. -/
theorem hasTemperateGrowth_finset_prod
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    {ι : Type*} {f : ι → E → R} {s : Finset ι}
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.prod_empty]
    exact Function.HasTemperateGrowth.const 1
  case insert a s' has ih =>
    simp only [Finset.prod_insert has]
    exact (hf _ (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Every monomial `x^α` on `ℝⁿ` has temperate growth: it is the product of coordinate-power
functions, each of which is of temperate growth. -/
theorem monomial_hasTemperateGrowth (α : Fin n → ℕ) :
    (monomial α).HasTemperateGrowth := by
  show (fun x : EuclideanSpace ℝ (Fin n) => ∏ i : Fin n, (↑(x i) : ℂ) ^ α i).HasTemperateGrowth
  apply hasTemperateGrowth_finset_prod
  intro i _
  suffices h : (fun x : EuclideanSpace ℝ (Fin n) => (↑(x i) : ℂ)).HasTemperateGrowth by
    have heq : (fun x : EuclideanSpace ℝ (Fin n) => (↑(x i) : ℂ) ^ α i) =
      ((fun x : EuclideanSpace ℝ (Fin n) => (↑(x i) : ℂ)) ^ α i) := by
      ext x; simp [Pi.pow_apply]
    rw [heq]
    exact h.pow (α i)
  convert (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).hasTemperateGrowth using 1

/-- Intermediate Sobolev-type representation of a tempered distribution: every `u ∈ 𝓢'(ℝⁿ, ℂ)`
can be written as a finite sum of pairings of `C₀` functions with iterated derivatives of the
Schwartz test function, indexed over a ball of multi-indices. This is the form (10.10) used
in the proof of Theorem 10.5 (Schwartz representation). -/
theorem sobolev_intermediate_form
    (n : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ) :=
  intermediate_form_eq1010 n u

/-- Leibniz-rule rewrite of the intermediate Sobolev representation: any expression of the
form `∑ c0SchwartzPairing (v γ) (∂^γ φ)` can be rewritten as a double sum over multi-indices
`(α, β)` of pairings against `∂^β (x^α · φ)`. -/
theorem leibniz_rewrite
    (n M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        (∑ γ ∈ multiIndicesBall n M,
          c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) =
        ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (f α β)
            (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) :=
  representation_rewrite n M v

/-- Schwartz representation theorem (Theorem 10.5 of Melrose), improved form: every tempered
distribution `u ∈ 𝓢'(ℝⁿ, ℂ)` is given by a finite sum over multi-indices `(α, β)` of
pairings of `C₀` functions `f α β` with `∂^β (x^α · φ)`. -/
theorem schwartz_representation_improved (n : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)),
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
        u φ = ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m,
          c0SchwartzPairing (f α β)
            (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) := by
  obtain ⟨M, v, hv⟩ := sobolev_intermediate_form n u
  obtain ⟨m, f, hf⟩ := leibniz_rewrite n M v
  exact ⟨m, f, fun φ => (hv φ).trans (hf φ)⟩

end SchwartzRepresentation

end
