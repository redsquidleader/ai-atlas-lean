/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution

set_option maxHeartbeats 200000

open scoped SchwartzMap
open MeasureTheory LineDeriv

noncomputable section

/-- A multi-index of dimension `n` is a tuple of natural numbers `Fin n → ℕ`. -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

/-- The order `|α| = α₁ + … + αₙ` of a multi-index. -/
def MultiIndex.order {n : ℕ} (α : MultiIndex n) : ℕ := ∑ i, α i

/-- Componentwise order on multi-indices: `α ≤ γ` iff `αᵢ ≤ γᵢ` for all `i`. -/
def MultiIndex.le {n : ℕ} (α γ : MultiIndex n) : Prop := ∀ i, α i ≤ γ i

/-- Decidability instance for the componentwise order on multi-indices. -/
instance MultiIndex.decidableLe {n : ℕ} (α γ : MultiIndex n) :
    Decidable (MultiIndex.le α γ) :=
  Fintype.decidableForallFintype

/-- Componentwise subtraction of multi-indices (with truncation at `0`). -/
def MultiIndex.sub {n : ℕ} (γ α : MultiIndex n) : MultiIndex n :=
  fun i => γ i - α i

/-- The finset of multi-indices `α` with `α ≤ γ`. -/
def MultiIndex.finsetLe {n : ℕ} (γ : MultiIndex n) : Finset (MultiIndex n) :=
  (Fintype.piFinset (fun i => Finset.range (γ i + 1))).filter (fun α => MultiIndex.le α γ)

/-- The `k`-fold iterated directional derivative of a tempered distribution `u`
in direction `m`. -/
def iteratedSingleDerivTD {n : ℕ}
    (m : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (lineDerivOp m)^[k] u

/-- The mixed partial derivative `∂^β = ∂_1^{β₁} ⋯ ∂_n^{βₙ}` of a tempered
distribution. -/
def multiDerivTD {n : ℕ}
    (β : MultiIndex n) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldl
    (fun acc i => iteratedSingleDerivTD (EuclideanSpace.single i 1) (β i) acc) u

/-- The monomial `x^α = x₁^{α₁} ⋯ xₙ^{αₙ}` as a complex-valued function on `ℝⁿ`. -/
def monomialFun {n : ℕ} (α : MultiIndex n) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => ∏ i, (↑(x i) : ℂ) ^ α i

/-- Multiplication of a tempered distribution by the monomial `x^α`. -/
def monomialMulTD {n : ℕ} (α : MultiIndex n)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ (monomialFun α) u

/-- The Japanese bracket `⟨x⟩ = √(1 + ‖x‖²)`. -/
def japaneseBracket {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (1 + ‖x‖ ^ 2)

/-- The complex-valued function `x ↦ ⟨x⟩^k`, where `⟨x⟩` is the Japanese bracket
and `k ∈ ℤ`. -/
def japaneseBracketZPow {n : ℕ} (k : ℤ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => ↑((japaneseBracket x) ^ k)

/-- Multiplication of a tempered distribution by `⟨x⟩^k`. -/
def japaneseBracketMulTD {n : ℕ} (k : ℤ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ (japaneseBracketZPow k) u

/-- Evaluate a multivariate polynomial `P ∈ ℂ[x₁,…,xₙ]` at a point `x ∈ ℝⁿ`. -/
def evalMvPoly {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  MvPolynomial.eval (fun i => ↑(x i)) P

/-- A tempered distribution is "from `C₀`" if it is represented by integration
against a continuous function vanishing at infinity. -/
def TemperedDistribution.IsFromC0 {n : ℕ}
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin n) → ℂ,
    Continuous g ∧
    Filter.Tendsto g (Filter.cocompact _) (nhds 0) ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      v φ = ∫ x, g x * φ x

/-- Theorem 10.5 (Schwartz representation): every tempered distribution can be
written as a finite sum of terms of the form `x^α ∂^β v` where each `v` is
represented by a continuous function vanishing at infinity. -/
theorem theorem_10_5_schwartz_representation (n : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (S : Finset (MultiIndex n × MultiIndex n))
      (v : MultiIndex n × MultiIndex n → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      (∀ p ∈ S, TemperedDistribution.IsFromC0 (v p)) ∧
      u = ∑ p ∈ S, monomialMulTD p.1 (multiDerivTD p.2 (v p)) := by sorry

/-- Lemma 10.6: a Leibniz-type expansion for `⟨x⟩^k ∂^γ v`, expressing the product
as a finite sum of derivatives `∂^{γ-α} ((polynomial · ⟨x⟩^{k - 2|γ-α|}) v)` whose
polynomial coefficients have controlled total degree. -/
theorem lemma_10_6_polynomial_weight_derivative {n : ℕ} (γ : MultiIndex n) (k : ℤ) :
    ∃ (P : MultiIndex n → MvPolynomial (Fin n) ℂ),
      (∀ α, MultiIndex.le α γ →
        (P α).totalDegree ≤ MultiIndex.order (MultiIndex.sub γ α)) ∧
      ∀ (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
        japaneseBracketMulTD k (multiDerivTD γ v) =
          ∑ α ∈ MultiIndex.finsetLe γ,
            multiDerivTD (MultiIndex.sub γ α)
              (TemperedDistribution.smulLeftCLM ℂ
                (fun x => evalMvPoly (P α) x *
                  japaneseBracketZPow
                    (k - 2 * ↑(MultiIndex.order (MultiIndex.sub γ α))) x)
                v) := by sorry

end
