/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HilbertSymbol
import Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import Atlas.ArithmeticGeometry.code.Hilbert2Adic
import Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

open scoped Classical

/-- A characteristic-zero field on which the Hilbert symbol is bilinear and nondegenerate.
The two structural axioms encode: (i) if both $(a,c)_F$ and $(b,c)_F$ equal $-1$ then
$(ab,c)_F = 1$ (used to derive bilinearity); (ii) for every non-square unit $c$ there
exists $b$ with $(b,c)_F = -1$ (nondegeneracy of the Hilbert pairing). -/
class HilbertBilinearField (F : Type*) [Field F] extends CharZero F where
  isSolvable_mul_of_both_neg : ∀ (a b c : Fˣ),
    hilbertSymbol F a c = -1 → hilbertSymbol F b c = -1 →
    hilbertSymbol F (a * b) c = 1
  nondegenerate : ∀ (c : Fˣ), ¬ IsSquare (c : F) →
    ∃ b : Fˣ, hilbertSymbol F b c = -1

section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

/-- Local variant: the Legendre symbol applied to `ZMod.val a` agrees with the quadratic
character of `ZMod p` evaluated at `a`. -/
lemma legendreSym_val_local (a : ZMod p) :
    legendreSym p (ZMod.val a : ℤ) = (quadraticChar (ZMod p)) a := by
  unfold legendreSym
  congr 1
  simp [ZMod.natCast_val]

/-- Multiplicativity of `padicUnitLegendre`: $\left(\frac{u_1 u_2}{p}\right) =
\left(\frac{u_1}{p}\right)\left(\frac{u_2}{p}\right)$. -/
lemma padicUnitLegendre_mul_local (u₁ u₂ : ℤ_[p]ˣ) :
    padicUnitLegendre (u₁ * u₂) = padicUnitLegendre u₁ * padicUnitLegendre u₂ := by
  simp only [padicUnitLegendre, legendreSym_val_local]
  rw [show PadicInt.toZMod ((u₁ * u₂ : ℤ_[p]ˣ) : ℤ_[p]) =
      PadicInt.toZMod (u₁ : ℤ_[p]) * PadicInt.toZMod (u₂ : ℤ_[p]) from by
    simp only [Units.val_mul, map_mul]]
  exact map_mul (quadraticChar (ZMod p)) _ _

/-- `padicUnitLegendre` always takes values in $\{\pm 1\}$ for an odd prime, since the
quadratic character of a nonzero element of $\mathbb{F}_p$ is $\pm 1$. -/
lemma padicUnitLegendre_eq_one_or_neg_one_local (v : ℤ_[p]ˣ) :
    padicUnitLegendre v = 1 ∨ padicUnitLegendre v = -1 := by
  simp only [padicUnitLegendre, legendreSym_val_local]
  have hne : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 := by
    intro h
    have hunit : IsUnit (PadicInt.toZMod (v : ℤ_[p])) := IsUnit.map PadicInt.toZMod v.isUnit
    exact not_isUnit_zero (h ▸ hunit)
  exact quadraticChar_dichotomy hne

/-- Every nonzero $p$-adic number can be written as $p^\alpha u$ with $\alpha \in \mathbb{Z}$
and $u \in \mathbb{Z}_p^\times$, i.e. $a = $ `padicPowerUnitZ p α u`. -/
lemma padic_unit_decomp (a : ℚ_[p]ˣ) :
    ∃ (α : ℤ) (u : ℤ_[p]ˣ), a = padicPowerUnitZ p α u := by
  set v := Padic.valuation (a : ℚ_[p]) with hv_def
  set w : ℚ_[p] := (a : ℚ_[p]) * (p : ℚ_[p]) ^ (-v) with hw_def
  have ha_ne : (a : ℚ_[p]) ≠ 0 := Units.ne_zero a

  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp.out)
  have hp_ne_zero_real : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp_ne_zero_qp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)

  have hw_norm : ‖w‖ = 1 := by
    rw [hw_def, norm_mul, Padic.norm_eq_zpow_neg_valuation ha_ne]
    rw [norm_zpow, Padic.norm_p]
    simp only [hv_def]
    rw [inv_zpow, ← zpow_neg, ← zpow_add₀ hp_ne_zero_real]
    simp

  have hw_padic_int : ‖w‖ ≤ 1 := by linarith
  set w_int : ℤ_[p] := ⟨w, hw_padic_int⟩ with hw_int_def
  have hw_unit : IsUnit w_int := by
    rw [PadicInt.isUnit_iff]
    exact hw_norm
  set u := hw_unit.unit with hu_def
  refine ⟨v, u, ?_⟩

  ext
  simp only [padicPowerUnitZ, Units.val_mul, Units.val_zpow_eq_zpow_val]
  show (a : ℚ_[p]) = ↑(qpPrime p) ^ v * ↑(unitZpToQp u)
  rw [qpPrime, Units.val_mk0, unitZpToQp_coe]
  have hu_eq : (u : ℤ_[p]) = w_int := by simp only [hu_def, IsUnit.unit_spec]
  rw [hu_eq, hw_int_def, Subtype.coe_mk, hw_def]
  rw [zpow_neg]
  field_simp

/-- The parity of $|\alpha_1 + \alpha_2|$ equals the parity of $|\alpha_1| + |\alpha_2|$. -/
lemma natAbs_add_mod_two (α₁ α₂ : ℤ) :
    (α₁ + α₂).natAbs % 2 = (α₁.natAbs + α₂.natAbs) % 2 := by
  have h1 : α₁.natAbs % 2 = (α₁ % 2).natAbs := by omega
  have h2 : α₂.natAbs % 2 = (α₂ % 2).natAbs := by omega
  have h3 : (α₁ + α₂).natAbs % 2 = ((α₁ + α₂) % 2).natAbs := by omega
  rw [h3]
  have h4 : (α₁ + α₂) % 2 = (α₁ % 2 + α₂ % 2) % 2 := by omega
  rw [h4]

  have hm1 : α₁ % 2 = 0 ∨ α₁ % 2 = 1 := by omega
  have hm2 : α₂ % 2 = 0 ∨ α₂ % 2 = 1 := by omega
  rcases hm1 with h | h <;> rcases hm2 with h' | h' <;> simp [h, h'] <;> omega

/-- Algebraic identity expressing bilinearity of the closed-form Hilbert formula in the
first argument, with all exponents written as natural-number absolute values and using
the square-equal-to-one hypotheses on the Legendre values. -/
lemma formula_bilinear_natAbs {m : ℕ} (α₁ α₂ γ : ℤ) (Lu₁ Lu₂ Lw : ℤ)
    (_hLu₁ : Lu₁ ^ 2 = 1) (_hLu₂ : Lu₂ ^ 2 = 1) (hLw : Lw ^ 2 = 1) :
    (-1 : ℤ) ^ ((α₁ + α₂).natAbs * γ.natAbs * m) *
      (Lu₁ * Lu₂) ^ γ.natAbs * Lw ^ (α₁ + α₂).natAbs =
    ((-1 : ℤ) ^ (α₁.natAbs * γ.natAbs * m) * Lu₁ ^ γ.natAbs * Lw ^ α₁.natAbs) *
    ((-1 : ℤ) ^ (α₂.natAbs * γ.natAbs * m) * Lu₂ ^ γ.natAbs * Lw ^ α₂.natAbs) := by

  have neg1_sq : (-1 : ℤ) ^ 2 = 1 := by norm_num
  have hmod_sum : (α₁ + α₂).natAbs % 2 = (α₁.natAbs + α₂.natAbs) % 2 :=
    natAbs_add_mod_two α₁ α₂

  rw [pow_eq_of_sq_eq_one_of_mod_two_eq hLw hmod_sum]

  have hmod_prod : ((α₁ + α₂).natAbs * γ.natAbs * m) % 2 =
      ((α₁.natAbs + α₂.natAbs) * γ.natAbs * m) % 2 := by
    rw [Nat.mul_mod ((α₁ + α₂).natAbs * γ.natAbs),
        Nat.mul_mod ((α₁.natAbs + α₂.natAbs) * γ.natAbs),
        Nat.mul_mod (α₁ + α₂).natAbs,
        Nat.mul_mod (α₁.natAbs + α₂.natAbs), hmod_sum]

  rw [pow_eq_of_sq_eq_one_of_mod_two_eq neg1_sq hmod_prod]

  rw [mul_pow, pow_add Lw]
  have : (α₁.natAbs + α₂.natAbs) * γ.natAbs * m =
      α₁.natAbs * γ.natAbs * m + α₂.natAbs * γ.natAbs * m := by ring
  rw [this, pow_add]
  ring

/-- For an odd prime $p$, a $p$-adic unit $v$ whose Legendre symbol is $1$ is a square in
$\mathbb{Z}_p$ (Hensel lifting from a square root mod $p$). -/
lemma padic_unit_square_of_legendre_one (hp_odd : p ≠ 2) (v : ℤ_[p]ˣ)
    (hv : padicUnitLegendre v = 1) : IsSquare (v : ℤ_[p]) := by


  simp only [padicUnitLegendre, legendreSym_val_local] at hv
  have hne : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 :=
    (RingHom.isUnit_map PadicInt.toZMod v.isUnit).ne_zero
  have hIsSquare : IsSquare (PadicInt.toZMod (v : ℤ_[p])) :=
    (quadraticChar_one_iff_isSquare hne).mp hv
  obtain ⟨s, hs⟩ := hIsSquare

  obtain ⟨s_lift, hs_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod s

  let f : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C (v : ℤ_[p])
  have hval : ‖Polynomial.aeval s_lift f‖ < 1 := by
    have hf_aeval : Polynomial.aeval s_lift f = s_lift ^ 2 - (v : ℤ_[p]) := by
      simp [f, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [hf_aeval, norm_lt_one_iff_toZMod_zero, map_sub, map_pow, hs_lift]
    rw [show PadicInt.toZMod (v : ℤ_[p]) = s * s from hs]
    ring
  have hs_unit : IsUnit s_lift := by
    rw [isUnit_iff_toZMod_ne_zero]; intro h0
    have : PadicInt.toZMod (v : ℤ_[p]) = 0 := by
      rw [hs, ← hs_lift, h0]; ring
    exact hne this
  have hderiv : ‖Polynomial.aeval s_lift f.derivative‖ = 1 := by
    have hf_deriv : Polynomial.aeval s_lift f.derivative = 2 * s_lift := by
      simp [f, Polynomial.derivative_sub, Polynomial.derivative_pow,
            Polynomial.derivative_X, Polynomial.derivative_C,
            Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [hf_deriv, norm_mul]
    have h2_unit : IsUnit (2 : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]; by_contra hne2; push Not at hne2
      have hlt2 : ‖(2 : ℤ_[p])‖ < 1 := lt_of_le_of_ne (2 : ℤ_[p]).2 hne2
      rw [PadicInt.norm_lt_one_iff_dvd] at hlt2; obtain ⟨k, hk⟩ := hlt2
      have h1 := congrArg PadicInt.toZMod hk
      simp only [map_ofNat, map_mul] at h1
      rw [toZMod_p_eq_zero, zero_mul] at h1
      have : (2 : ZMod p) ≠ 0 := by
        rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
            ZMod.natCast_eq_zero_iff]; intro hdvd
        exact hp_odd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) (Nat.Prime.two_le hp.out))
      exact this h1
    rw [PadicInt.isUnit_iff.mp h2_unit, PadicInt.isUnit_iff.mp hs_unit, mul_one]
  obtain ⟨z, hz_root, _⟩ := (hensel_lemma_norm f s_lift hval hderiv).exists
  have hz_sq : z ^ 2 = (v : ℤ_[p]) := by
    have h := hz_root
    simp [f, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
    exact sub_eq_zero.mp h
  exact ⟨z, by rw [← hz_sq, sq]⟩

/-- If $v$ is a square in $\mathbb{Z}_p$ and $\gamma$ has even absolute value, then
$p^\gamma v$ is a square in $\mathbb{Q}_p$. -/
lemma padicPowerUnitZ_isSquare_of_unit_sq_even_val (v : ℤ_[p]ˣ)
    (hv_sq : IsSquare (v : ℤ_[p])) (k : ℕ) (hk : γ.natAbs = k + k) :
    IsSquare ((padicPowerUnitZ p γ v : ℚ_[p]ˣ) : ℚ_[p]) := by
  obtain ⟨z, hz⟩ := hv_sq


  have hγ_even : Even γ := by
    have : Even γ.natAbs := ⟨k, hk⟩
    rwa [Int.natAbs_even] at this
  obtain ⟨m, hm⟩ := hγ_even
  have hc_val : ((padicPowerUnitZ p γ v : ℚ_[p]ˣ) : ℚ_[p]) =
      ((↑p : ℚ_[p]) ^ m) ^ 2 * ((z : ℚ_[p]) ^ 2) := by
    simp only [padicPowerUnitZ, Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [qpPrime, Units.val_mk0, hm, unitZpToQp_coe]
    have : (↑p : ℚ_[p]) ^ (m + m) = ((↑p : ℚ_[p]) ^ m) ^ 2 := by
      rw [sq]
      have hp_ne : (↑p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
      exact zpow_add₀ hp_ne m m
    rw [this, hz]
    push_cast
    ring
  rw [hc_val]
  exact ⟨(↑p : ℚ_[p]) ^ m * (z : ℚ_[p]), by ring⟩

end PadicBilinearHelpers

section TwoAdicBridgeLocal

open PadicInt HilbertSymbol

/-- Bridge: existence of a primitive mod-$8$ solution for $z^2 = ux^2 + vy^2$ over
$\mathbb{Z}_2$ is equivalent to the decidable predicate on the mod-$8$ reductions. -/
lemma hasPrimSolMod8_one_eq_local (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_one u v ↔
    hasPrimSolMod8_one_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
  simp only [HasPrimitiveSolutionMod8_one, hasPrimSolMod8_one_dec, toZModPow_unit_coe]

/-- Bridge: existence of a primitive mod-$8$ solution for $z^2 = 2u x^2 + v y^2$ over
$\mathbb{Z}_2$ is equivalent to the decidable predicate on the mod-$8$ reductions. -/
lemma hasPrimSolMod8_two_eq_local (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_two u v ↔
    hasPrimSolMod8_two_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
  simp only [HasPrimitiveSolutionMod8_two, hasPrimSolMod8_two_dec, toZModPow_unit_coe]

/-- Glue lemma: given that the Hilbert symbol equals $1$ iff there is a primitive solution,
that primitive solvability is equivalent to a decidable mod-$8$ predicate, and the formula
is $\pm 1$ matching the predicate, conclude that the Hilbert symbol equals the formula. -/
lemma hilbert_eq_formula_of_iff_local
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

/-- Theorem 10.9, case $(\alpha,\beta) = (0,0)$: the $2$-adic Hilbert symbol on unit
inputs $(u, v)$ equals the closed-form formula at $(0,0)$. -/
lemma thm_10_9_one_one_local (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_one v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 0 :=
  hilbert_eq_formula_of_iff_local
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_one u) (padicUnit_one v))
    ((lemma_10_8_one u v).trans (hasPrimSolMod8_one_eq_local u v))
    (formula_eq_one_or_neg_one _ _ 0 0)
    (formula_one_one_verified _ _)

/-- Theorem 10.9, case $(\alpha,\beta) = (1,0)$: $(2u, v)_{\mathbb{Q}_2}$ equals the
closed-form formula at $(1, 0)$. -/
lemma thm_10_9_two_one_local (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_one v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 0 :=
  hilbert_eq_formula_of_iff_local
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two u) (padicUnit_one v))
    ((lemma_10_8_two u v).trans (hasPrimSolMod8_two_eq_local u v))
    (formula_eq_one_or_neg_one _ _ 1 0)
    (formula_two_one_verified _ _)

/-- Symmetry of the Hilbert symbol over $\mathbb{Q}_2$: $(a, b)_{\mathbb{Q}_2} =
(b, a)_{\mathbb{Q}_2}$ (local instance of the general symmetry, swapping $(x,y)$). -/
lemma hilbertSymbol_symm_local (a b : ℚ_[2]ˣ) :
    hilbertSymbol ℚ_[2] a b = hilbertSymbol ℚ_[2] b a := by
  unfold hilbertSymbol
  have h : HilbertSymbol.IsSolvable ℚ_[2] a b ↔ HilbertSymbol.IsSolvable ℚ_[2] b a := by
    constructor
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
  simp_rw [show HilbertSymbol.IsSolvable ℚ_[2] a b = HilbertSymbol.IsSolvable ℚ_[2] b a from propext h]

/-- Theorem 10.9, case $(\alpha,\beta) = (0,1)$: $(u, 2v)_{\mathbb{Q}_2}$ equals the
closed-form formula at $(0, 1)$, obtained from the $(1,0)$ case by symmetry. -/
lemma thm_10_9_one_two_local (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 1 := by
  rw [show padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) =
               padicHilbertSymbol 2 (padicUnit_two v) (padicUnit_one u) from
    hilbertSymbol_symm_local _ _]
  exact hilbert_eq_formula_of_iff_local
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two v) (padicUnit_one u))
    ((lemma_10_8_two v u).trans (hasPrimSolMod8_two_eq_local v u))
    (formula_eq_one_or_neg_one _ _ 0 1)
    (formula_one_two_verified _ _)

/-- Multiplicativity of the mod-$8$ reduction on units:
`toZModPow_unit 3 (u * v) = toZModPow_unit 3 u * toZModPow_unit 3 v`. -/
lemma toZModPow_unit_mul (u v : ℤ_[2]ˣ) :
    toZModPow_unit 3 (u * v) = toZModPow_unit 3 u * toZModPow_unit 3 v := by
  ext
  simp only [toZModPow_unit_coe, Units.val_mul, map_mul]


/-- Theorem 10.9, case $(\alpha,\beta) = (1,1)$: $(2u, 2v)_{\mathbb{Q}_2}$ equals the
closed-form formula at $(1, 1)$. This is the remaining case completing Theorem 10.9. -/
theorem padic_hilbert_bilinear_p2_two_two_case (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_two v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 1 := by sorry

/-- Theorem 10.9, case $(\alpha,\beta) = (1,1)$: wrapper around
`padic_hilbert_bilinear_p2_two_two_case` matching the naming convention of the other cases. -/
lemma thm_10_9_two_two_local (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_two v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 1 :=
  padic_hilbert_bilinear_p2_two_two_case u v

/-- Theorem 10.9 in unified form: for $\alpha, \beta \in \{0,1\}$ and units $u, v \in \mathbb{Z}_2^\times$,
the $2$-adic Hilbert symbol $(2^\alpha u, 2^\beta v)_{\mathbb{Q}_2}$ equals the closed-form
formula at $(\alpha, \beta)$. -/
lemma hilbert_formula_2adic_fin2 (α β : Fin 2) (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicPowerUnit 2 α u) (padicPowerUnit 2 β v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) (α : ℕ) (β : ℕ) := by
  fin_cases α <;> fin_cases β <;> simp only [padicPowerUnit, Fin.val_zero, Fin.val_one,
    pow_zero, one_mul, pow_one]
  ·
    exact thm_10_9_one_one_local u v
  ·
    show padicHilbertSymbol 2 (unitZpToQp u) (qpPrime 2 * unitZpToQp v) = _
    rw [show (qpPrime 2 * unitZpToQp v : ℚ_[2]ˣ) = padicUnit_two v from by
      ext; simp [padicUnit_two_val, qpPrime, unitZpToQp_coe, Units.val_mk0, Units.val_mul]]
    rw [show (unitZpToQp u : ℚ_[2]ˣ) = padicUnit_one u from by
      ext; simp [padicUnit_one_val, unitZpToQp_coe]]
    exact thm_10_9_one_two_local u v
  ·
    show padicHilbertSymbol 2 (qpPrime 2 * unitZpToQp u) (unitZpToQp v) = _
    rw [show (qpPrime 2 * unitZpToQp u : ℚ_[2]ˣ) = padicUnit_two u from by
      ext; simp [padicUnit_two_val, qpPrime, unitZpToQp_coe, Units.val_mk0, Units.val_mul]]
    rw [show (unitZpToQp v : ℚ_[2]ˣ) = padicUnit_one v from by
      ext; simp [padicUnit_one_val, unitZpToQp_coe]]
    exact thm_10_9_two_one_local u v
  ·
    show padicHilbertSymbol 2 (qpPrime 2 * unitZpToQp u) (qpPrime 2 * unitZpToQp v) = _
    rw [show (qpPrime 2 * unitZpToQp u : ℚ_[2]ˣ) = padicUnit_two u from by
      ext; simp [padicUnit_two_val, qpPrime, unitZpToQp_coe, Units.val_mk0, Units.val_mul]]
    rw [show (qpPrime 2 * unitZpToQp v : ℚ_[2]ˣ) = padicUnit_two v from by
      ext; simp [padicUnit_two_val, qpPrime, unitZpToQp_coe, Units.val_mk0, Units.val_mul]]
    exact thm_10_9_two_two_local u v

/-- Theorem 10.9 in fully general form: for $\alpha, \beta \in \mathbb{Z}$ and units
$u, v \in \mathbb{Z}_2^\times$, $(2^\alpha u, 2^\beta v)_{\mathbb{Q}_2}$ equals the closed-form
formula at $(\alpha \bmod 2, \beta \bmod 2)$, using that the symbol is unchanged by even
shifts in the valuation. -/
lemma hilbert_formula_2adic_general (α β : ℤ) (u v : ℤ_[2]ˣ) :
    padicHilbertSymbol 2 (padicPowerUnitZ 2 α u) (padicPowerUnitZ 2 β v) =
    hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v)
      (α % 2).toNat (β % 2).toNat := by
  let α' : Fin 2 := ⟨(α % 2).toNat, int_emod_two_toNat_lt α⟩
  let β' : Fin 2 := ⟨(β % 2).toNat, int_emod_two_toNat_lt β⟩

  have hL : hilbertSymbol ℚ_[2] (padicPowerUnitZ 2 α u) (padicPowerUnitZ 2 β v) =
      hilbertSymbol ℚ_[2] (padicPowerUnit 2 α' u) (padicPowerUnitZ 2 β v) := by
    unfold padicPowerUnitZ padicPowerUnit
    conv_lhs => rw [show α = 2 * (α / 2) + α % 2 from (Int.ediv_add_emod α 2).symm]
    rw [zpow_add, zpow_mul]
    have hsq : (qpPrime 2 ^ (2 : ℤ)) ^ (α / 2) = (qpPrime 2 ^ (α / 2)) ^ (2 : ℕ) := by
      rw [← zpow_natCast (qpPrime 2 ^ (α / 2)) 2, ← zpow_mul, ← zpow_mul, mul_comm]; norm_cast
    rw [hsq, show (qpPrime 2 ^ (α / 2)) ^ 2 * qpPrime 2 ^ (α % 2) * unitZpToQp u =
      (qpPrime 2 ^ (α / 2)) ^ 2 * (qpPrime 2 ^ (α % 2) * unitZpToQp u) from by group]
    rw [hilbert_sq_mul_left]
    congr 1; congr 1
    rcases Int.emod_two_eq_zero_or_one α with h | h <;> simp [α', h, zpow_natCast]

  have hR : hilbertSymbol ℚ_[2] (padicPowerUnit 2 α' u) (padicPowerUnitZ 2 β v) =
      hilbertSymbol ℚ_[2] (padicPowerUnit 2 α' u) (padicPowerUnit 2 β' v) := by
    unfold padicPowerUnitZ padicPowerUnit
    conv_lhs => rw [show β = 2 * (β / 2) + β % 2 from (Int.ediv_add_emod β 2).symm]
    rw [zpow_add, zpow_mul]
    have hsq : (qpPrime 2 ^ (2 : ℤ)) ^ (β / 2) = (qpPrime 2 ^ (β / 2)) ^ (2 : ℕ) := by
      rw [← zpow_natCast (qpPrime 2 ^ (β / 2)) 2, ← zpow_mul, ← zpow_mul, mul_comm]; norm_cast
    rw [hsq, show (qpPrime 2 ^ (β / 2)) ^ 2 * qpPrime 2 ^ (β % 2) * unitZpToQp v =
      (qpPrime 2 ^ (β / 2)) ^ 2 * (qpPrime 2 ^ (β % 2) * unitZpToQp v) from by group]
    rw [hilbert_sq_mul_right]
    congr 1; congr 1
    rcases Int.emod_two_eq_zero_or_one β with h | h <;> simp [β', h, zpow_natCast]
  simp only [padicHilbertSymbol]; rw [hL, hR]
  exact hilbert_formula_2adic_fin2 α' β' u v

end TwoAdicBridgeLocal

open HilbertSymbol PadicInt in
/-- Half of bilinearity over $\mathbb{Q}_2$: if $(a, c)_{\mathbb{Q}_2} = (b, c)_{\mathbb{Q}_2} = -1$,
then $(ab, c)_{\mathbb{Q}_2} = 1$. Reduced via the $p$-adic decomposition and the closed-form
formula to the verified bilinearity lemma `formula_mul_left_core`. -/
theorem padic_isSolvable_mul_of_both_neg_p2
    [hp : Fact (Nat.Prime 2)] :
    ∀ (a b c : ℚ_[2]ˣ),
      hilbertSymbol ℚ_[2] a c = -1 → hilbertSymbol ℚ_[2] b c = -1 →
      hilbertSymbol ℚ_[2] (a * b) c = 1 := by
  intro a b c hac hbc
  obtain ⟨α₁, u₁, ha_eq⟩ := padic_unit_decomp a
  obtain ⟨α₂, u₂, hb_eq⟩ := padic_unit_decomp b
  obtain ⟨γ, w, hc_eq⟩ := padic_unit_decomp c
  rw [ha_eq] at hac ⊢; rw [hb_eq] at hbc ⊢; rw [hc_eq] at hac hbc ⊢
  change padicHilbertSymbol 2 _ _ = -1 at hac
  change padicHilbertSymbol 2 _ _ = -1 at hbc
  change padicHilbertSymbol 2 _ _ = 1
  have hab_eq : padicPowerUnitZ 2 α₁ u₁ * padicPowerUnitZ 2 α₂ u₂ =
      padicPowerUnitZ 2 (α₁ + α₂) (u₁ * u₂) := by
    simp only [padicPowerUnitZ]; rw [zpow_add]; simp only [unitZpToQp]
    ext; simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, Units.val_mul]; ring
  rw [hab_eq]

  rw [hilbert_formula_2adic_general] at hac hbc ⊢
  rw [toZModPow_unit_mul]


  set a1 : Fin 2 := ⟨(α₁ % 2).toNat, int_emod_two_toNat_lt α₁⟩
  set a2 : Fin 2 := ⟨(α₂ % 2).toNat, int_emod_two_toNat_lt α₂⟩
  set g : Fin 2 := ⟨(γ % 2).toNat, int_emod_two_toNat_lt γ⟩


  have hperiod : hilbert2Adic_formula (toZModPow_unit 3 u₁ * toZModPow_unit 3 u₂)
      (toZModPow_unit 3 w) ((α₁ + α₂) % 2).toNat (γ % 2).toNat =
    hilbert2Adic_formula (toZModPow_unit 3 u₁ * toZModPow_unit 3 u₂)
      (toZModPow_unit 3 w) ((a1 : ℕ) + (a2 : ℕ)) (g : ℕ) := by
    simp only [hilbert2Adic_formula]; congr 1

    have h_cast_sum : ((((α₁ + α₂) % 2).toNat : ℕ) : ZMod 2) =
        ((((a1 : ℕ) + (a2 : ℕ)) : ℕ) : ZMod 2) := by
      simp only [a1, a2, Fin.val_mk]; push_cast
      have h_cast_mod2 : ∀ n : ℤ, (((n % 2).toNat : ℕ) : ZMod 2) = ((n : ℤ) : ZMod 2) := fun n => by
        have key : ((n % 2 : ℤ) : ZMod 2) = ((n : ℤ) : ZMod 2) :=
          (ZMod.intCast_eq_intCast_iff' (n % 2) n 2).mpr (by omega)
        rw [← key]
        rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]
      rw [h_cast_mod2, h_cast_mod2, h_cast_mod2]; push_cast; ring
    rw [h_cast_sum]
  rw [hperiod]

  rw [formula_mul_left_core
    (toZModPow_unit 3 u₁) (toZModPow_unit 3 u₂) (toZModPow_unit 3 w) a1 a2 g,
    hac, hbc]
  norm_num

open HilbertSymbol in


/-- Half of bilinearity over $\mathbb{Q}_p$ for arbitrary primes $p$: if
$(a,c)_{\mathbb{Q}_p} = (b,c)_{\mathbb{Q}_p} = -1$ then $(ab,c)_{\mathbb{Q}_p} = 1$.
The case $p = 2$ is `padic_isSolvable_mul_of_both_neg_p2`; the odd case uses the closed-form
formula together with multiplicativity of the Legendre symbol. -/
theorem padic_isSolvable_mul_of_both_neg_ax (p : ℕ) [Fact p.Prime] :
    ∀ (a b c : ℚ_[p]ˣ),
      hilbertSymbol ℚ_[p] a c = -1 → hilbertSymbol ℚ_[p] b c = -1 →
      hilbertSymbol ℚ_[p] (a * b) c = 1 := by
  by_cases hp2 : p = 2
  · subst hp2; exact padic_isSolvable_mul_of_both_neg_p2
  · intro a b c hac hbc

    obtain ⟨α₁, u₁, ha_eq⟩ := padic_unit_decomp a
    obtain ⟨α₂, u₂, hb_eq⟩ := padic_unit_decomp b
    obtain ⟨γ, w, hc_eq⟩ := padic_unit_decomp c
    rw [ha_eq] at hac ⊢
    rw [hb_eq] at hbc ⊢
    rw [hc_eq] at hac hbc ⊢


    change padicHilbertSymbol p _ _ = -1 at hac
    change padicHilbertSymbol p _ _ = -1 at hbc
    change padicHilbertSymbol p _ _ = 1
    rw [hilbert_formula_odd_general hp2] at hac hbc

    have hab_eq : padicPowerUnitZ p α₁ u₁ * padicPowerUnitZ p α₂ u₂ =
        padicPowerUnitZ p (α₁ + α₂) (u₁ * u₂) := by
      simp only [padicPowerUnitZ]
      rw [zpow_add]
      simp only [unitZpToQp]
      ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
      simp only [map_mul, Units.val_mul]
      ring
    rw [hab_eq]
    rw [hilbert_formula_odd_general hp2]


    rw [padicUnitLegendre_mul_local]
    rw [formula_bilinear_natAbs α₁ α₂ γ
      (padicUnitLegendre u₁) (padicUnitLegendre u₂) (padicUnitLegendre w)
      (padicUnitLegendre_sq u₁) (padicUnitLegendre_sq u₂) (padicUnitLegendre_sq w)]
    rw [hac, hbc]
    norm_num

section Nondeg2Adic_Computational

attribute [-instance] Classical.propDecidable

/-- Local copy (within this `Nondeg2Adic_Computational` section, with classical decidability
disabled) of the decidable predicate for primitive mod-$8$ solvability of
$z^2 = u_0 x^2 + v_0 y^2$. -/
@[reducible] def hasPrimSolMod8_one_loc (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

/-- Local copy (within `Nondeg2Adic_Computational`) of the decidable predicate for primitive
mod-$8$ solvability of $z^2 = 2 u_0 x^2 + v_0 y^2$. -/
@[reducible] def hasPrimSolMod8_two_loc (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 +
              (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

/-- Decidability of `hasPrimSolMod8_one_loc` via finite search over `ZMod 8`. -/
instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_one_loc u₀ v₀) :=
  Fintype.decidableExistsFintype
/-- Decidability of `hasPrimSolMod8_two_loc` via finite search over `ZMod 8`. -/
instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_two_loc u₀ v₀) :=
  Fintype.decidableExistsFintype


/-- Decidable witness predicate for $2$-adic nondegeneracy: a unit $w_0 \in (\mathbb{Z}/8)^\times$
has either a unit $v_0$ with $z^2 = v_0 x^2 + w_0 y^2$ insolvable mod $8$, or a unit $v_0$
with $z^2 = 2v_0 x^2 + w_0 y^2$ insolvable mod $8$. -/
@[reducible] def nondeg_unit_combined (w₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  (∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_one_loc v₀ w₀) ∨
  (∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_two_loc v₀ w₀)

/-- Decidability of `nondeg_unit_combined` from decidability of each disjunct. -/
instance (w₀ : (ZMod (2 ^ 3))ˣ) : Decidable (nondeg_unit_combined w₀) :=
  instDecidableOr

/-- Brute-force verification: every non-identity unit $w_0 \in (\mathbb{Z}/8)^\times$ admits a
witness of nondegeneracy in the `nondeg_unit_combined` sense, used in the $p = 2$ case of
the nondegeneracy axiom. -/
lemma nondeg_mod8_unit_witness :
    ∀ (w₀ : (ZMod (2 ^ 3))ˣ), w₀ ≠ 1 → nondeg_unit_combined w₀ := by
  native_decide


/-- Decidable predicate: a unit $w_0 \in (\mathbb{Z}/8)^\times$ admits some unit $v_0$ for
which $z^2 = 2 w_0 x^2 + v_0 y^2$ is insolvable mod $8$. Used for nondegeneracy when the
valuation of $c$ is odd. -/
@[reducible] def nondeg_two_prop (w₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_two_loc w₀ v₀

/-- Decidability of `nondeg_two_prop` via finite search over $(\mathbb{Z}/8)^\times$. -/
instance (w₀ : (ZMod (2 ^ 3))ˣ) : Decidable (nondeg_two_prop w₀) :=
  Fintype.decidableExistsFintype

/-- Brute-force verification: every unit $w_0 \in (\mathbb{Z}/8)^\times$ satisfies
`nondeg_two_prop`. Used for nondegeneracy when $c = 2^{\text{odd}} w$. -/
lemma nondeg_mod8_two_witness :
    ∀ (w₀ : (ZMod (2 ^ 3))ˣ), nondeg_two_prop w₀ := by
  native_decide

end Nondeg2Adic_Computational

open HilbertSymbol

/-- Reduction modulo $8$ of a $2$-adic unit, producing a unit of $\mathbb{Z}/8$. -/
noncomputable def toZMod8Unit (w : ℤ_[2]ˣ) : (ZMod (2 ^ 3))ˣ :=
  ((PadicInt.isUnit_toZModPow_iff (show 0 < 3 from by omega)).mpr w.isUnit).unit

/-- The underlying element of `toZMod8Unit w` is `PadicInt.toZModPow 3 (↑w)`. -/
lemma toZMod8Unit_val (w : ℤ_[2]ˣ) :
    (↑(toZMod8Unit w) : ZMod (2 ^ 3)) = PadicInt.toZModPow 3 (↑w : ℤ_[2]) :=
  IsUnit.unit_spec _

/-- Bridge: primitive mod-$8$ solvability of $z^2 = ux^2 + vy^2$ over $\mathbb{Z}_2$ is
equivalent to the local decidable predicate on `toZMod8Unit u` and `toZMod8Unit v`. -/
lemma hasPrimSolMod8_one_iff (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_one u v ↔ hasPrimSolMod8_one_loc (toZMod8Unit u) (toZMod8Unit v) := by
  simp only [HasPrimitiveSolutionMod8_one, hasPrimSolMod8_one_loc, toZMod8Unit_val]

/-- Bridge: primitive mod-$8$ solvability of $z^2 = 2u x^2 + v y^2$ over $\mathbb{Z}_2$ is
equivalent to the local decidable predicate on `toZMod8Unit u` and `toZMod8Unit v`. -/
lemma hasPrimSolMod8_two_iff (u v : ℤ_[2]ˣ) :
    HasPrimitiveSolutionMod8_two u v ↔ hasPrimSolMod8_two_loc (toZMod8Unit u) (toZMod8Unit v) := by
  simp only [HasPrimitiveSolutionMod8_two, hasPrimSolMod8_two_loc, toZMod8Unit_val]

/-- Surjectivity of `toZMod8Unit`: every unit in $\mathbb{Z}/8$ lifts to some unit in
$\mathbb{Z}_2$. -/
lemma toZMod8Unit_surj (u₀ : (ZMod (2 ^ 3))ˣ) :
    ∃ u : ℤ_[2]ˣ, toZMod8Unit u = u₀ := by
  obtain ⟨x, hx⟩ := PadicInt.toZModPow_surjective' 3 (↑u₀ : ZMod (2 ^ 3))
  have hxu : IsUnit x := (PadicInt.isUnit_toZModPow_iff (show 0 < 3 from by omega)).mp
    (hx ▸ u₀.isUnit)
  refine ⟨hxu.unit, ?_⟩
  ext
  simp only [toZMod8Unit_val, IsUnit.unit_spec]
  exact hx


/-- The underlying $\mathbb{Q}_2$-value of `padicUnit_one w` equals the image of $w$ under
`unitZpToQp`, i.e. the embedding $\mathbb{Z}_2^\times \hookrightarrow \mathbb{Q}_2^\times$. -/
lemma padicUnit_one_eq_unitZpToQp (w : ℤ_[2]ˣ) :
    (padicUnit_one w : ℚ_[2]) = (unitZpToQp w : ℚ_[2]) := by
  simp [padicUnit_one_val, unitZpToQp_coe]

/-- Unit-level version of `padicUnit_one_eq_unitZpToQp`: equality in $\mathbb{Q}_2^\times$. -/
lemma padicUnit_one_eq_unitZpToQp' (w : ℤ_[2]ˣ) :
    padicUnit_one w = unitZpToQp w := by
  ext; exact padicUnit_one_eq_unitZpToQp w

/-- The underlying $\mathbb{Q}_2$-value of `padicUnit_two w` factors as $2 \cdot w$. -/
lemma padicUnit_two_eq_qpPrime_mul (w : ℤ_[2]ˣ) :
    (padicUnit_two w : ℚ_[2]) = (qpPrime 2 : ℚ_[2]) * (unitZpToQp w : ℚ_[2]) := by
  simp [padicUnit_two_val, unitZpToQp_coe, qpPrime, Units.val_mk0]

/-- Unit-level version of `padicUnit_two_eq_qpPrime_mul`: equality in $\mathbb{Q}_2^\times$. -/
lemma padicUnit_two_eq_qpPrime_mul' (w : ℤ_[2]ˣ) :
    padicUnit_two w = qpPrime 2 * unitZpToQp w := by
  ext; exact padicUnit_two_eq_qpPrime_mul w


open HilbertSymbol in
/-- Nondegeneracy of the $2$-adic Hilbert pairing: for every non-square unit
$c \in \mathbb{Q}_2^\times$ there exists $b \in \mathbb{Q}_2^\times$ with
$(b, c)_{\mathbb{Q}_2} = -1$. Proven by lifting an obstruction from the mod-$8$ witnesses
`nondeg_mod8_unit_witness`/`nondeg_mod8_two_witness`. -/
theorem padic_nondegenerate_p2
    [hp : Fact (Nat.Prime 2)] :
    ∀ (c : ℚ_[2]ˣ), ¬ IsSquare (c : ℚ_[2]) →
      ∃ b : ℚ_[2]ˣ, hilbertSymbol ℚ_[2] b c = -1 := by
  intro c hc
  obtain ⟨γ, w, hc_eq⟩ := padic_unit_decomp c

  rcases Int.even_or_odd γ with ⟨m, hm⟩ | ⟨m, hm⟩
  ·

    have hc_sq : c = (qpPrime 2) ^ m * (qpPrime 2) ^ m * unitZpToQp w := by
      rw [hc_eq, padicPowerUnitZ, hm]; group


    have huw_nsq : ¬ IsSquare ((unitZpToQp w : ℚ_[2]ˣ) : ℚ_[2]) := by
      intro ⟨s, hs⟩
      apply hc
      refine ⟨(qpPrime 2) ^ m * s, ?_⟩
      rw [hc_sq]; simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [hs]; push_cast; ring


    have hw_ne_one : toZMod8Unit w ≠ 1 := by
      intro h
      apply huw_nsq

      have hmod : PadicInt.toZModPow 3 (↑w : ℤ_[2]) = 1 := by
        rw [← toZMod8Unit_val, h]; simp

      have hdvd : (2 : ℤ_[2]) ^ 3 ∣ 1 * 1 ^ 2 - (↑w : ℤ_[2]) := by
        rw [one_mul, one_pow]
        rw [show (2 : ℤ_[2]) ^ 3 = ((2 : ℕ) : ℤ_[2]) ^ 3 from by norm_cast]
        rw [← PadicInt.toZModPow_eq_zero_iff_dvd]
        simp only [map_sub, map_one, hmod, sub_self]
      obtain ⟨z', hz', _⟩ := exists_mul_sq_eq_of_mod8 isUnit_one isUnit_one hdvd
      rw [one_mul] at hz'
      refine ⟨(z' : ℚ_[2]), ?_⟩
      rw [unitZpToQp_coe]
      have hsq : (↑w : ℤ_[2]) = z' * z' := by rw [← sq]; exact hz'.symm
      have := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) hsq
      push_cast at this ⊢; exact this

    obtain hw_wit := nondeg_mod8_unit_witness (toZMod8Unit w) hw_ne_one
    rcases hw_wit with ⟨v₀, hv₀⟩ | ⟨v₀, hv₀⟩
    ·
      obtain ⟨v, hv_eq⟩ := toZMod8Unit_surj v₀
      refine ⟨padicUnit_one v, ?_⟩
      have hc_rw : c = (qpPrime 2 ^ m) ^ 2 * padicUnit_one w := by
        rw [hc_sq, padicUnit_one_eq_unitZpToQp']; group
      rw [hc_rw, hilbert_sq_mul_right]
      rw [hilbertSymbol.eq_neg_one_iff]
      intro hsol
      apply hv₀
      rw [← hv_eq, ← hasPrimSolMod8_one_iff]
      exact (lemma_10_8_one v w).mp
        ((isSolvable_iff_hasPrimitiveSolution _ _).mp
          (by rwa [padicUnit_one_eq_unitZpToQp'] at hsol))
    ·
      obtain ⟨v, hv_eq⟩ := toZMod8Unit_surj v₀
      refine ⟨padicUnit_two v, ?_⟩
      have hc_rw : c = (qpPrime 2 ^ m) ^ 2 * padicUnit_one w := by
        rw [hc_sq, padicUnit_one_eq_unitZpToQp']; group
      rw [hc_rw, hilbert_sq_mul_right]
      rw [hilbertSymbol.eq_neg_one_iff]
      intro hsol
      apply hv₀
      rw [← hv_eq, ← hasPrimSolMod8_two_iff]
      exact (lemma_10_8_two v w).mp
        ((isSolvable_iff_hasPrimitiveSolution _ _).mp
          (by rwa [padicUnit_one_eq_unitZpToQp'] at hsol))
  ·

    have hc_sq : c = (qpPrime 2) ^ m * (qpPrime 2) ^ m *
        (qpPrime 2 * unitZpToQp w) := by
      rw [hc_eq, padicPowerUnitZ, hm]; group

    obtain ⟨v₀, hv₀⟩ := nondeg_mod8_two_witness (toZMod8Unit w)
    obtain ⟨v, hv_eq⟩ := toZMod8Unit_surj v₀


    refine ⟨padicUnit_one v, ?_⟩
    have hc_rw : c = (qpPrime 2 ^ m) ^ 2 * padicUnit_two w := by
      rw [hc_sq, padicUnit_two_eq_qpPrime_mul']; group
    rw [hc_rw, hilbert_sq_mul_right]
    rw [hilbert_symm]
    rw [hilbertSymbol.eq_neg_one_iff]
    intro hsol
    apply hv₀
    rw [← hv_eq, ← hasPrimSolMod8_two_iff]
    exact (lemma_10_8_two w v).mp
      ((isSolvable_iff_hasPrimitiveSolution _ _).mp hsol)

open HilbertSymbol in


/-- Nondegeneracy of the $p$-adic Hilbert pairing for every prime $p$. For odd $p$, uses a
quadratic non-residue $u_{\text{nr}}$ and the closed-form formula; for $p = 2$ uses
`padic_nondegenerate_p2`. -/
theorem padic_nondegenerate_ax (p : ℕ) [Fact p.Prime] :
    ∀ (c : ℚ_[p]ˣ), ¬ IsSquare (c : ℚ_[p]) →
      ∃ b : ℚ_[p]ˣ, hilbertSymbol ℚ_[p] b c = -1 := by
  by_cases hp2 : p = 2
  · subst hp2; exact padic_nondegenerate_p2
  · intro c hc

    obtain ⟨γ, w, hc_eq⟩ := padic_unit_decomp c


    have hrc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp2

    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hrc
    have ha_ne : a ≠ 0 := by intro h; rw [h, MulChar.map_zero] at ha; exact absurd ha (by norm_num)
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective PadicInt.toZMod a
    have hx_unit : IsUnit x := (isUnit_iff_toZMod_ne_zero x).mpr (hx ▸ ha_ne)
    set u_nr := hx_unit.unit with hu_nr_def
    have hL_nr : padicUnitLegendre u_nr = -1 := by
      simp only [padicUnitLegendre, legendreSym_val_local]
      rw [show (u_nr : ℤ_[p]) = x from IsUnit.unit_spec hx_unit]
      rw [hx]
      exact ha

    rcases Nat.even_or_odd γ.natAbs with ⟨k, hk⟩ | ⟨k, hk⟩
    ·

      have hLw : padicUnitLegendre w = -1 := by
        rcases padicUnitLegendre_eq_one_or_neg_one_local w with hLw | hLw
        ·
          exfalso; apply hc

          have hw_sq := padic_unit_square_of_legendre_one hp2 w hLw
          rw [hc_eq, show ((padicPowerUnitZ p γ w : ℚ_[p]ˣ) : ℚ_[p]) =
              ((padicPowerUnitZ p γ w : ℚ_[p]ˣ) : ℚ_[p]) from rfl]
          exact padicPowerUnitZ_isSquare_of_unit_sq_even_val w hw_sq k hk
        · exact hLw

      refine ⟨padicPowerUnitZ p 1 1, ?_⟩
      rw [hc_eq]
      change padicHilbertSymbol p _ _ = -1
      rw [hilbert_formula_odd_general hp2]

      have hL1 : padicUnitLegendre (1 : ℤ_[p]ˣ) = 1 := by
        simp only [padicUnitLegendre, Units.val_one, map_one, ZMod.val_one p]
        exact legendreSym.at_one p
      simp only [Int.natAbs_one]
      rw [hk, hL1, hLw]
      simp only [one_pow, mul_one, pow_one]

      have : 1 * (k + k) * ((p - 1) / 2) = 2 * (k * ((p - 1) / 2)) := by ring
      rw [this, pow_mul, neg_one_sq, one_pow]
      norm_num
    ·
      refine ⟨padicPowerUnitZ p 0 u_nr, ?_⟩
      rw [hc_eq]
      change padicHilbertSymbol p _ _ = -1
      rw [hilbert_formula_odd_general hp2]
      simp only [Int.natAbs_zero, zero_mul, pow_zero, mul_one, one_mul]


      rw [hL_nr, hk]
      simp [pow_succ, pow_mul]

/-- The $p$-adic field $\mathbb{Q}_p$ is a `HilbertBilinearField`: the Hilbert symbol
$(-,-)_{\mathbb{Q}_p}$ is bilinear and nondegenerate. -/
noncomputable instance instHilbertBilinearFieldPadic (p : ℕ) [Fact p.Prime] : HilbertBilinearField ℚ_[p] where
  isSolvable_mul_of_both_neg := padic_isSolvable_mul_of_both_neg_ax p
  nondegenerate := padic_nondegenerate_ax p

/-- A nonzero real number that is not a square must be negative (since nonnegative reals
admit square roots). -/
lemma real_unit_not_square_neg (c : ℝˣ) (hc : ¬ IsSquare (c : ℝ)) : (c : ℝ) < 0 := by
  by_contra h
  push Not at h
  apply hc
  have hpos : 0 < (c : ℝ) := lt_of_le_of_ne h (Ne.symm c.ne_zero)
  exact ⟨Real.sqrt c, by rw [← sq, Real.sq_sqrt hpos.le]⟩

/-- If $a > 0$ is real, then $z^2 = a x^2 + b y^2$ is solvable with $(x, y, z) = (1/\sqrt{a}, 0, 1)$,
so the real Hilbert symbol $(a, b)_{\mathbb{R}} = 1$ for any $b$. -/
lemma real_pos_isSolvable (a : ℝˣ) (ha : 0 < (a : ℝ)) (b : ℝˣ) :
    HilbertSymbol.IsSolvable ℝ a b := by
  refine ⟨1 / Real.sqrt a, 0, ?_⟩
  simp only [mul_zero, sq (0 : ℝ), add_zero]
  rw [div_pow, one_pow, Real.sq_sqrt ha.le]
  field_simp

/-- If $(a, c)_{\mathbb{R}} = -1$ then $a < 0$ (contrapositive of `real_pos_isSolvable`). -/
lemma real_hilbert_neg_one_imp_neg_left (a c : ℝˣ)
    (h : hilbertSymbol ℝ a c = -1) : (a : ℝ) < 0 := by
  by_contra ha
  push Not at ha
  have hpos : 0 < (a : ℝ) := lt_of_le_of_ne ha (Ne.symm a.ne_zero)
  rw [hilbertSymbol.eq_neg_one_iff] at h
  exact h (real_pos_isSolvable a hpos c)

/-- If $(a, c)_{\mathbb{R}} = -1$ then $c < 0$ (symmetric counterpart of the previous lemma). -/
lemma real_hilbert_neg_one_imp_neg_right (a c : ℝˣ)
    (h : hilbertSymbol ℝ a c = -1) : (c : ℝ) < 0 := by
  by_contra hc
  push Not at hc
  have hpos : 0 < (c : ℝ) := lt_of_le_of_ne hc (Ne.symm c.ne_zero)
  rw [hilbertSymbol.eq_neg_one_iff] at h
  apply h
  refine ⟨0, 1 / Real.sqrt c, ?_⟩
  simp only [mul_zero, sq (0 : ℝ), zero_add]
  rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
  field_simp

/-- The real field $\mathbb{R}$ is a `HilbertBilinearField`: bilinearity holds because two
negative reals multiply to a positive one, and nondegeneracy holds because $-1$ pairs nontrivially
with itself. -/
noncomputable instance instHilbertBilinearFieldReal : HilbertBilinearField ℝ where
  isSolvable_mul_of_both_neg := by
    intro a b c ha hb
    have ha_neg : (a : ℝ) < 0 := real_hilbert_neg_one_imp_neg_left a c ha
    have hb_neg : (b : ℝ) < 0 := real_hilbert_neg_one_imp_neg_left b c hb
    have hab_pos : 0 < ((a * b : ℝˣ) : ℝ) := by
      simp only [Units.val_mul]
      exact mul_pos_of_neg_of_neg ha_neg hb_neg
    rw [hilbertSymbol.eq_one_iff]
    exact real_pos_isSolvable (a * b) hab_pos c
  nondegenerate := by
    intro c hc
    have hc_neg : (c : ℝ) < 0 := real_unit_not_square_neg c hc
    refine ⟨c, ?_⟩
    rw [hilbertSymbol.eq_neg_one_iff]
    rintro ⟨x, y, h⟩
    have h1 : (c : ℝ) * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_neg.le (sq_nonneg x)
    have h2 : (c : ℝ) * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_neg.le (sq_nonneg y)
    linarith

namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- Wrapper exposing `HilbertBilinearField.isSolvable_mul_of_both_neg` in the
`hilbertSymbol` namespace. -/
theorem isSolvable_mul_of_both_neg [HilbertBilinearField F]
    (a b c : Fˣ)
    (ha : hilbertSymbol F a c = -1) (hb : hilbertSymbol F b c = -1) :
    hilbertSymbol F (a * b) c = 1 :=
  HilbertBilinearField.isSolvable_mul_of_both_neg a b c ha hb

/-- Symmetry of the Hilbert symbol over any field: $(a, b)_F = (b, a)_F$ (swap $(x, y)$ in
the defining equation $z^2 = a x^2 + b y^2$). -/
theorem symm (a b : Fˣ) : hilbertSymbol F a b = hilbertSymbol F b a := by
  unfold hilbertSymbol
  have h : HilbertSymbol.IsSolvable F a b ↔ HilbertSymbol.IsSolvable F b a := by
    constructor
    · rintro ⟨x, y, h⟩
      exact ⟨y, x, by rw [add_comm]; exact h⟩
    · rintro ⟨x, y, h⟩
      exact ⟨y, x, by rw [add_comm]; exact h⟩
  simp_rw [show HilbertSymbol.IsSolvable F a b = HilbertSymbol.IsSolvable F b a from propext h]

/-- Bilinearity in the left argument: $(ab, c)_F = (a, c)_F \cdot (b, c)_F$ for any
`HilbertBilinearField` $F$. -/
theorem mul_left [HilbertBilinearField F] (a b c : Fˣ) :
    hilbertSymbol F (a * b) c = hilbertSymbol F a c * hilbertSymbol F b c := by
  rcases eq_one_or_neg_one a c with hac | hac
  · exact (hilbert_mul_of_eq_one a b c hac).symm
  · rcases eq_one_or_neg_one b c with hbc | hbc
    · rw [show a * b = b * a from mul_comm a b]
      have key := (hilbert_mul_of_eq_one b a c hbc).symm
      rw [key, hbc, one_mul]; ring
    · rw [isSolvable_mul_of_both_neg a b c hac hbc, hac, hbc]; norm_num

/-- Bilinearity in the right argument: $(a, bc)_F = (a, b)_F \cdot (a, c)_F$, derived from
symmetry and `mul_left`. -/
theorem mul_right [HilbertBilinearField F] (a b c : Fˣ) :
    hilbertSymbol F a (b * c) = hilbertSymbol F a b * hilbertSymbol F a c := by
  rw [symm a (b * c), mul_left, symm b a, symm c a]

/-- Nondegeneracy axiom of `HilbertBilinearField`, exposed in the `hilbertSymbol` namespace:
every non-square unit pairs to $-1$ with some element. -/
theorem nondegenerate [HilbertBilinearField F] (c : Fˣ) (hc : ¬ IsSquare (c : F)) :
    ∃ b : Fˣ, hilbertSymbol F b c = -1 :=
  HilbertBilinearField.nondegenerate c hc

end hilbertSymbol
