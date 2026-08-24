/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Hilbert2Adic
import Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
import Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions

open PadicInt HilbertSymbol

noncomputable section

/-- The function $\varepsilon(u) = (u - 1) / 2 \pmod{2}$ applied to a $2$-adic unit $u$, computed
via its image in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
def epsilon_padic (u : ℤ_[2]ˣ) : ZMod 2 :=
  epsilon_ZMod8 (toZModPow_unit 3 u)

/-- The function $\omega(u) = (u^2 - 1) / 8 \pmod{2}$ applied to a $2$-adic unit $u$, computed
via its image in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
def omega_padic (u : ℤ_[2]ˣ) : ZMod 2 :=
  omega_ZMod8 (toZModPow_unit 3 u)

/-- The mod-$8$ primitive solution condition for type-one ($u x^2 + v y^2 \equiv z^2$) can be
checked using a decidable version on the images in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
lemma hasPrimSolMod8_one_eq (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_one u v ↔
    hasPrimSolMod8_one_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
  simp only [HasPrimitiveSolutionMod8_one, hasPrimSolMod8_one_dec, toZModPow_unit_coe]

/-- The mod-$8$ primitive solution condition for type-two (involving the factor $2$) can be
checked using a decidable version on the images in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
lemma hasPrimSolMod8_two_eq (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_two u v ↔
    hasPrimSolMod8_two_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
  simp only [HasPrimitiveSolutionMod8_two, hasPrimSolMod8_two_dec, toZModPow_unit_coe]

/-- Bridge between the abstract Hilbert symbol and a concrete formula $f \in \{1, -1\}$:
if the Hilbert symbol equals $1$ iff the form has a primitive solution, and the latter is
equivalent to a decidable mod-$8$ condition expressed by $f = 1$, then the Hilbert symbol
equals $f$. -/
lemma hilbert_eq_formula_of_iff
    {a b : ℚ_[2]ˣ}
    (h_iff : padicHilbertSymbol 2 a b = 1 ↔ HasPrimitiveSolution a b)
    {solMod : Prop} [Decidable solMod]
    (h_lift : HasPrimitiveSolution a b ↔ solMod)
    {f : ℤ} (hf : f = 1 ∨ f = -1)
    (h_formula : solMod ↔ f = 1) :
    padicHilbertSymbol 2 a b = f := by
  rcases padicHilbertSymbol.eq_one_or_neg_one a b with h | h
  · rw [h]
    rcases hf with hf1 | hf1
    · exact hf1.symm
    · exfalso
      have hsol : solMod := h_lift.mp (h_iff.mp h)
      rw [h_formula.mp hsol] at hf1; exact absurd hf1 (by omega)
  · rw [h]
    rcases hf with hf1 | hf1
    · exfalso
      have hf1' : f = 1 := hf1
      rw [← h_formula] at hf1'
      have := h_lift.mpr hf1'
      rw [← h_iff] at this
      rw [this] at h; exact absurd h (by omega)
    · exact hf1.symm

/-- The element $2 \in \mathbb{Q}_2^\times$, viewed as a unit. -/
noncomputable def twoQp : ℚ_[2]ˣ := (isUnit_of_invertible (2 : ℚ_[2])).unit

/-- The underlying value of the unit `twoQp` is $2$. -/
lemma twoQp_val : (twoQp : ℚ_[2]) = 2 := IsUnit.unit_spec _

/-- Decomposition of a "type-two" $2$-adic unit (of the form $2 \cdot v$) as the product
$2 \cdot v$. -/
lemma padicUnit_two_eq_mul (v : ℤ_[2]ˣ) :
    padicUnit_two v = twoQp * padicUnit_one v := by
  ext
  simp only [padicUnit_two_val, twoQp_val, padicUnit_one_val, Units.val_mul]

/-- Decomposition of a "type-two" $2$-adic unit as $u \cdot 2$ (commuted form). -/
lemma padicUnit_two_eq_mul' (u : ℤ_[2]ˣ) :
    padicUnit_two u = padicUnit_one u * twoQp := by
  ext
  simp only [padicUnit_two_val, twoQp_val, padicUnit_one_val, Units.val_mul, mul_comm]

/-- The unit $2 \in \mathbb{Q}_2^\times$ equals the type-two unit with multiplier $1$. -/
lemma twoQp_eq_padicUnit_two_one : twoQp = padicUnit_two 1 := by
  ext
  simp only [twoQp_val, padicUnit_two_val, Units.val_one]
  push_cast
  ring

/-- The element $-1 \in \mathbb{Q}_2^\times$ equals the type-one unit coming from
$-1 \in \mathbb{Z}_2^\times$. -/
lemma neg_one_eq_padicUnit_one : (-1 : ℚ_[2]ˣ) = padicUnit_one (-1 : ℤ_[2]ˣ) := by
  ext
  simp only [padicUnit_one_val, Units.val_neg, Units.val_one]
  push_cast
  ring

/-- The image of $1 \in \mathbb{Z}_2^\times$ under reduction to
$(\mathbb{Z}/8\mathbb{Z})^\times$ is $1$. -/
lemma toZModPow_unit_one : toZModPow_unit 3 (1 : ℤ_[2]ˣ) = 1 := by
  ext
  simp only [toZModPow_unit_coe, Units.val_one, map_one]

/-- The image of $-1 \in \mathbb{Z}_2^\times$ under reduction to
$(\mathbb{Z}/8\mathbb{Z})^\times$ is $-1$. -/
lemma toZModPow_unit_neg_one : toZModPow_unit 3 (-1 : ℤ_[2]ˣ) = -1 := by
  ext
  simp only [toZModPow_unit_coe, Units.val_neg, Units.val_one, map_neg, map_one]

/-- **Theorem 10.9 (case unit-unit).** For $2$-adic units $u, v$, the Hilbert symbol
$(u, v)_2$ equals the explicit formula $(-1)^{\varepsilon(u)\varepsilon(v)}$. -/
theorem thm_10_9_one_one (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_one v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 0 := by
  exact hilbert_eq_formula_of_iff
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_one u) (padicUnit_one v))
    ((lemma_10_8_one u v).trans (hasPrimSolMod8_one_eq u v))
    (formula_eq_one_or_neg_one _ _ 0 0)
    (formula_one_one_verified _ _)

/-- **Theorem 10.9 (case $2u$-unit).** Hilbert symbol formula for $(2u, v)_2$ with
$u, v \in \mathbb{Z}_2^\times$. -/
theorem thm_10_9_two_one (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_one v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 0 := by
  exact hilbert_eq_formula_of_iff
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two u) (padicUnit_one v))
    ((lemma_10_8_two u v).trans (hasPrimSolMod8_two_eq u v))
    (formula_eq_one_or_neg_one _ _ 1 0)
    (formula_two_one_verified _ _)

/-- **Theorem 10.9 (case unit-$2v$).** Hilbert symbol formula for $(u, 2v)_2$ with
$u, v \in \mathbb{Z}_2^\times$, obtained from `thm_10_9_two_one` by symmetry. -/
theorem thm_10_9_one_two (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 1 := by

  rw [show padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) =
               padicHilbertSymbol 2 (padicUnit_two v) (padicUnit_one u) from
    hilbertSymbol.symm _ _]
  exact hilbert_eq_formula_of_iff
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two v) (padicUnit_one u))
    ((lemma_10_8_two v u).trans (hasPrimSolMod8_two_eq v u))
    (formula_eq_one_or_neg_one _ _ 0 1)
    (formula_one_two_verified _ _)

/-- **Theorem 10.9 (case $2u$-$2v$).** Hilbert symbol formula for $(2u, 2v)_2$ with
$u, v \in \mathbb{Z}_2^\times$, obtained by bilinearity from the unit-unit and mixed cases. -/
theorem thm_10_9_two_two (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_two v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 1 := by

  have h1 : padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_two v) =
      padicHilbertSymbol 2 (padicUnit_two u) twoQp *
      padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_one v) := by
    simp only [padicHilbertSymbol]
    rw [padicUnit_two_eq_mul v, hilbertSymbol.mul_right]

  have h2 : padicHilbertSymbol 2 (padicUnit_two u) twoQp =
      padicHilbertSymbol 2 (padicUnit_one u) twoQp *
      padicHilbertSymbol 2 twoQp twoQp := by
    simp only [padicHilbertSymbol]
    rw [padicUnit_two_eq_mul' u, hilbertSymbol.mul_left]

  have h3 : padicHilbertSymbol 2 (padicUnit_one u) twoQp =
      padicHilbertSymbol 2 twoQp (padicUnit_one u) :=
    hilbertSymbol.symm _ _

  have h4 : padicHilbertSymbol 2 twoQp twoQp =
      hilbertSymbol ℚ_[2] (-1) twoQp :=
    hilbertSymbol.hilbert_self_eq_neg_one twoQp

  have h5 : padicHilbertSymbol 2 twoQp (padicUnit_one u) =
      hilbert2Adic_formula (toZModPow_unit 3 (1 : ℤ_[2]ˣ)) (toZModPow_unit 3 u) 1 0 := by
    rw [twoQp_eq_padicUnit_two_one]
    exact thm_10_9_two_one 1 u

  have h6 : hilbertSymbol ℚ_[2] (-1) twoQp =
      hilbert2Adic_formula (toZModPow_unit 3 (-1 : ℤ_[2]ˣ)) (toZModPow_unit 3 (1 : ℤ_[2]ˣ)) 0 1 := by
    rw [neg_one_eq_padicUnit_one, twoQp_eq_padicUnit_two_one]
    exact thm_10_9_one_two (-1) 1

  have h7 := thm_10_9_two_one u v

  rw [h1, h2, h3, h4, h5, h6, h7]

  rw [toZModPow_unit_one, toZModPow_unit_neg_one]

  exact (formula_bilinear_identity _ _).symm

end
