/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HilbertSymbol

open PadicInt HilbertSymbol

/-- Reduction of a $2$-adic unit `u : ℤ_[2]ˣ` to a unit in `ZMod (2 ^ n)` via `toZModPow`. -/
noncomputable def toZModPow_unit (n : ℕ) (u : ℤ_[2]ˣ) : (ZMod (2 ^ n))ˣ :=
  (Units.isUnit u).map (toZModPow n : ℤ_[2] →+* ZMod (2 ^ n)) |>.unit

/-- The underlying element of `toZModPow_unit n u` agrees with `toZModPow n (↑u)`. -/
lemma toZModPow_unit_coe (n : ℕ) (u : ℤ_[2]ˣ) :
    (toZModPow_unit n u : ZMod (2 ^ n)) = toZModPow n (↑u) :=
  IsUnit.unit_spec _

/-- Decidable predicate: there exist `x₀, y₀, z₀ ∈ ZMod 8` with at least one a unit such
that $z_0^2 = u_0 x_0^2 + v_0 y_0^2$ (primitive solution mod $8$ for the case $\alpha = 0$). -/
@[reducible]
def hasPrimSolMod8_one_dec (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

/-- Decidable predicate: there exist `x₀, y₀, z₀ ∈ ZMod 8` with at least one a unit such
that $z_0^2 = 2 u_0 x_0^2 + v_0 y_0^2$ (primitive solution mod $8$ for the case $\alpha = 1$). -/
@[reducible]
def hasPrimSolMod8_two_dec (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 +
              (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_one_dec u₀ v₀) :=
  inferInstance

instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_two_dec u₀ v₀) :=
  inferInstance

/-- The invariant $\epsilon(u) = (u - 1)/2 \bmod 2$ for a unit `u` in `ZMod 8`. -/
def epsilon_ZMod8 (u : (ZMod (2 ^ 3))ˣ) : ZMod 2 :=
  ((((u : ZMod (2 ^ 3)).val - 1) / 2 : ℕ) : ZMod 2)

/-- The invariant $\omega(u) = (u^2 - 1)/8 \bmod 2$ for a unit `u` in `ZMod 8`. -/
def omega_ZMod8 (u : (ZMod (2 ^ 3))ˣ) : ZMod 2 :=
  ((((u : ZMod (2 ^ 3)).val ^ 2 - 1) / 8 : ℕ) : ZMod 2)

/-- The closed-form expression $(-1)^{\epsilon(u)\epsilon(v) + \alpha\omega(v) + \beta\omega(u)}$
for the $2$-adic Hilbert symbol on units (Theorem 10.9). -/
def hilbert2Adic_formula
    (u₀ v₀ : (ZMod (2 ^ 3))ˣ) (α β : ℕ) : ℤ :=
  (-1 : ℤ) ^ ((epsilon_ZMod8 u₀ * epsilon_ZMod8 v₀ +
    α * omega_ZMod8 v₀ + β * omega_ZMod8 u₀).val)

/-- Brute-force verification: primitive solvability of $z^2 = u_0 x^2 + v_0 y^2$ mod $8$
agrees with the closed-form formula at $(\alpha,\beta) = (0,0)$. -/
lemma formula_one_one_verified :
    ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ,
      hasPrimSolMod8_one_dec u₀ v₀ ↔ hilbert2Adic_formula u₀ v₀ 0 0 = 1 := by
  native_decide

/-- Brute-force verification: primitive solvability of $z^2 = 2u_0 x^2 + v_0 y^2$ mod $8$
agrees with the closed-form formula at $(\alpha,\beta) = (1,0)$. -/
lemma formula_two_one_verified :
    ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ,
      hasPrimSolMod8_two_dec u₀ v₀ ↔ hilbert2Adic_formula u₀ v₀ 1 0 = 1 := by
  native_decide

/-- Brute-force verification: primitive solvability of $z^2 = u_0 x^2 + 2v_0 y^2$ mod $8$
(equivalently the swap of the previous lemma) agrees with the formula at $(\alpha,\beta) = (0,1)$. -/
lemma formula_one_two_verified :
    ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ,
      hasPrimSolMod8_two_dec v₀ u₀ ↔ hilbert2Adic_formula u₀ v₀ 0 1 = 1 := by
  native_decide

/-- Algebraic identity used to reduce the case $(\alpha,\beta) = (1,1)$ of the $2$-adic
Hilbert symbol to the other three cases via bilinearity. -/
lemma formula_bilinear_identity :
    ∀ u₀ v₀ : (ZMod (2 ^ 3))ˣ,
      hilbert2Adic_formula u₀ v₀ 1 1 =
      hilbert2Adic_formula (1 : (ZMod (2 ^ 3))ˣ) u₀ 1 0 *
      hilbert2Adic_formula (-1 : (ZMod (2 ^ 3))ˣ) (1 : (ZMod (2 ^ 3))ˣ) 0 1 *
      hilbert2Adic_formula u₀ v₀ 1 0 := by native_decide

/-- The closed-form formula always evaluates to $\pm 1$, since it is a power of $-1$. -/
lemma formula_eq_one_or_neg_one (u₀ v₀ : (ZMod (2 ^ 3))ˣ) (α β : ℕ) :
    hilbert2Adic_formula u₀ v₀ α β = 1 ∨ hilbert2Adic_formula u₀ v₀ α β = -1 := by
  unfold hilbert2Adic_formula
  exact neg_one_pow_eq_or ℤ _

/-- Bilinearity of the closed-form formula in the left $2$-adic unit argument,
verified by brute force over the finite cases. -/
lemma formula_mul_left_core :
    ∀ (u₁ u₂ w : (ZMod (2 ^ 3))ˣ) (α₁ α₂ γ : Fin 2),
      hilbert2Adic_formula (u₁ * u₂) w ((α₁ : ℕ) + (α₂ : ℕ)) (γ : ℕ) =
      hilbert2Adic_formula u₁ w (α₁ : ℕ) (γ : ℕ) *
      hilbert2Adic_formula u₂ w (α₂ : ℕ) (γ : ℕ) := by native_decide
