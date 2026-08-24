/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators

open scoped SchwartzMap
open TemperedDistribution MvPolynomial

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}


/-- An elliptic parametrix for the constant-coefficient differential operator with symbol `P`:
a tempered distribution `E` such that `P(D) E - δ₀` is smooth and `E` has singular support at
the origin only. Existence is provided by `parametrix_exists_with_singSupp`. -/
def ellipticParametrix (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (parametrix_exists_with_singSupp hP).choose


/-- The chosen elliptic parametrix is indeed a parametrix for `P`: it satisfies
`P(D) (ellipticParametrix m P hP) = δ₀ + ω` for some smooth `ω`. -/
theorem ellipticParametrix_isParametrix (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) : IsParametrix P (ellipticParametrix m P hP) :=
  (parametrix_exists_with_singSupp hP).choose_spec.1


/-- The singular support of the elliptic parametrix is contained in `{0}`, reflecting that
elliptic parametrices have a singularity only at the origin. -/
theorem ellipticParametrix_singularSupport (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) :
    singularSupport (ellipticParametrix m P hP) ⊆ {(0 : EuclideanSpace ℝ (Fin n))} :=
  (parametrix_exists_with_singSupp hP).choose_spec.2

/-- Elliptic operators are hypoelliptic: this packages the existence of a parametrix with
singular support at the origin, which implies that solutions of `P(D) u = f` have the same
singular support as `f`. -/
theorem elliptic_isHypoelliptic (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) : IsHypoelliptic P :=
  ⟨ellipticParametrix m P hP,
   ellipticParametrix_isParametrix m P hP,
   ellipticParametrix_singularSupport m P hP⟩

end DifferentialOperators

end
