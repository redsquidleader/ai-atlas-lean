/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch
import Mathlib.FieldTheory.RatFunc.Basic

open RiemannRochSpace CurveDivisor CurveWithOrd

namespace RiemannRochSpace

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]

/-- A rational curve (function field $\cong k(t)$) has trivial $\mathrm{Pic}^0$ (every degree-$0$ divisor is principal) and infinitely many points. -/
theorem rational_curve_Pic0_and_infinite
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k) :
    (∀ (D : CurveDivisor C), degree C D = 0 →
      ∃ f : Fˣ, principalDivisor (C := C) (F := F) f = D) ∧
    (∃ f : ℕ → C, Function.Injective f) := by sorry

/-- A rational curve admits an injection from $\mathbb{N}$, witnessing it has infinitely many points. -/
theorem rational_curve_inject_nat
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k) :
    ∃ f : ℕ → C, Function.Injective f :=
  (rational_curve_Pic0_and_infinite hF).2

/-- A rational curve has infinitely many points. -/
theorem rational_curve_infinite
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k) :
    Infinite C :=
  let ⟨f, hf⟩ := rational_curve_inject_nat hF
  Infinite.of_injective f hf

/-- Every degree-zero divisor on a rational curve is principal. -/
theorem degree_zero_divisor_is_principal_of_rational
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k)
    (D : CurveDivisor C) (hD : degree C D = 0) :
    ∃ f : Fˣ, principalDivisor (C := C) (F := F) f = D :=
  (rational_curve_Pic0_and_infinite hF).1 D hD

/-- $\mathrm{Pic}^0(C) = 0$ for a rational curve: every divisor of degree $0$ is principal. -/
theorem Pic0_trivial_of_rational
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k) :
    ∀ (D : CurveDivisor C), degree C D = 0 →
      ∃ f : Fˣ, principalDivisor (C := C) (F := F) f = D :=
  fun D hD => degree_zero_divisor_is_principal_of_rational hF D hD


/-- A nonzero rational function $f$ has prescribed poles given by an effective divisor $A$ if $\mathrm{div}(f) + A \geq 0$ and $\mathrm{ord}_P(f) = -A(P)$ for every $P$ with $A(P) > 0$. -/
def HasPrescribedPoles (f : Fˣ) (A : CurveDivisor C) : Prop :=
  (principalDivisor (C := C) f + A).IsEffective ∧
  ∀ P : C, A P > 0 → CurveWithOrd.ord (F := F) P f = -(A P)

/-- On a rational curve (hence infinite), any divisor $A$ admits a point $P_0$ outside its support. -/
theorem exists_point_not_in_support
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k)
    (A : CurveDivisor C) :
    ∃ P₀ : C, P₀ ∉ A.support := by
  haveI := rational_curve_infinite (C := C) hF
  exact Infinite.exists_notMem_finset A.support

/-- On a rational curve, given any effective divisor $A$ of positive degree, there exists a rational function $f$ with prescribed poles equal to $A$. -/
theorem prescribed_poles_of_rational
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k)
    (A : CurveDivisor C) (_hA : A.IsEffective) (hA_pos : degree C A > 0) :
    ∃ f : Fˣ, HasPrescribedPoles (C := C) (F := F) (k := k) f A := by


  obtain ⟨P₀, hP₀⟩ := exists_point_not_in_support hF A

  let d := degree C A
  let D : CurveDivisor C := -A + Finsupp.single P₀ d

  have hD_deg : degree C D = 0 := by
    show degree C (-A + Finsupp.single P₀ d) = 0
    rw [degree_add, degree_neg, degree_single]
    omega

  obtain ⟨f, hf⟩ := degree_zero_divisor_is_principal_of_rational hF D hD_deg

  refine ⟨f, ?eff, ?ord_eq⟩

  ·

    intro P
    rw [hf]
    show (-A + Finsupp.single P₀ d + A) P ≥ 0
    simp only [Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply]
    have : (-A P + Finsupp.single P₀ d P + A P) = Finsupp.single P₀ d P := by omega
    rw [this]
    by_cases hP : P = P₀
    · simp [hP]; omega
    · rw [Finsupp.single_eq_of_ne hP]

  ·
    intro P hAP

    have hPne : P ≠ P₀ := by
      intro heq
      rw [heq] at hAP
      exact absurd (Finsupp.mem_support_iff.mpr (by omega)) hP₀

    rw [← principalDivisor_apply (C := C) (F := F) f P, hf]
    show (-A + Finsupp.single P₀ d) P = -(A P)
    simp only [Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply]
    have hP0 : Finsupp.single P₀ d P = 0 := Finsupp.single_eq_of_ne hPne
    rw [hP0]
    omega

/-- A function with prescribed poles bounded by $A$ lies in the Riemann-Roch space $L(A)$. -/
theorem mem_riemannRochSpace_of_prescribed_poles
    {f : Fˣ} {A : CurveDivisor C}
    (hf : HasPrescribedPoles (C := C) (F := F) (k := k) f A) :
    (f : F) ∈ riemannRochSpace (F := F) (k := k) A := by
  rw [mem_riemannRochSpace_iff]
  right
  refine ⟨Units.ne_zero f, ?_⟩
  have : Units.mk0 (↑f) (Units.ne_zero f) = f := Units.mk0_val f _
  rw [this]
  exact hf.1

/-- If $A \leq B$ as divisors then $\deg B - \deg A \geq 0$. -/
theorem degree_sub_nonneg_of_le
    {C : Type*} {A B : CurveDivisor C} (hAB : A ≤ B) :
    0 ≤ degree C B - degree C A := by
  have hBA_eff := (CurveDivisor.le_iff_isEffective_sub A B).mp hAB
  have h0 : 0 ≤ degree C (B - A) := by
    rw [CurveDivisor.degree_eq_sum]
    exact Finsupp.sum_nonneg (fun i _ => hBA_eff i)
  linarith [degree_sub B A]


/-- Inductive step lemma for Riemann-Roch on $\mathbb{P}^1$: when $A \leq B$ are effective with $\deg B - \deg A = n$, we have $\dim_k L(B) = \dim_k L(A) + (\deg B - \deg A)$, proved by induction on $n$. -/
theorem step_eq_aux
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k)
    (n : ℕ)
    {A B : CurveDivisor C} (hAB : A ≤ B) (hA : A.IsEffective)
    [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)]
    (hn : (degree C B - degree C A).toNat = n) :
    (Module.finrank k (riemannRochSpace (F := F) (k := k) B) : ℤ) =
    (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) +
      (degree C B - degree C A) := by
  induction n generalizing A B with
  | zero =>

    have hdeg_nonneg := degree_sub_nonneg_of_le hAB
    have hdeg_eq : degree C B = degree C A := by omega

    have hAB_eq : A = B := by
      classical
      ext P
      by_contra hne
      have hlt : A P < B P := lt_of_le_of_ne (hAB P)
        (by intro heq; exact hne heq)
      have hBA_eff := (CurveDivisor.le_iff_isEffective_sub A B).mp hAB

      have hBA_ne : B - A ≠ 0 := by
        intro h
        have := Finsupp.ext_iff.mp h P
        simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at this
        omega
      have : 0 < degree C (B - A) := by
        rw [CurveDivisor.degree_eq_sum]
        apply Finsupp.sum_pos
        · intro i hi
          rw [Finsupp.mem_support_iff] at hi
          have := hBA_eff i
          omega
        · exact hBA_ne

      rw [degree_sub] at this; omega
    subst hAB_eq
    simp
  | succ m ih =>
    have hdeg_nonneg := degree_sub_nonneg_of_le hAB

    have hAB_ne : A ≠ B := by
      intro heq; subst heq; simp at hn
    have : ∃ P, A P < B P := by
      by_contra hall
      push Not at hall
      exact hAB_ne (Finsupp.ext (fun P => le_antisymm (hAB P) (hall P)))
    obtain ⟨P₀, hP₀⟩ := this

    set A' := A + Finsupp.single P₀ 1 with hA'_def

    have hAA' : A ≤ A' := by
      intro Q
      simp only [hA'_def, Finsupp.coe_add, Pi.add_apply]
      have : 0 ≤ Finsupp.single P₀ (1 : ℤ) Q := by
        by_cases hQ : Q = P₀
        · simp [hQ]
        · rw [Finsupp.single_eq_of_ne hQ]
      omega

    have hA'B : A' ≤ B := by
      intro Q
      simp only [hA'_def, Finsupp.coe_add, Pi.add_apply]
      by_cases hQ : Q = P₀
      · subst hQ; rw [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_eq_of_ne hQ]; simp; exact hAB Q

    have hA'_eff : A'.IsEffective := by
      intro Q
      have hAQ := hA Q
      simp only [hA'_def, Finsupp.coe_add, Pi.add_apply]
      by_cases hQ : Q = P₀
      · subst hQ; rw [Finsupp.single_eq_same]; linarith
      · rw [Finsupp.single_eq_of_ne hQ]; simp; exact hAQ


    have hdeg_A' : degree C A' = degree C A + 1 := by
      rw [hA'_def, degree_add, degree_single]

    have h218_AA' := riemannRochSpace_finrank_le_of_le (F := F) (k := k) hAA'
    haveI hfd_A' : FiniteDimensional k (riemannRochSpace (F := F) (k := k) A') := h218_AA'.1

    have hub_AA' : (Module.finrank k (riemannRochSpace (F := F) (k := k) A') : ℤ) ≤
        (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) + 1 := by
      have := h218_AA'.2
      rw [hdeg_A'] at this; linarith

    have hdeg_A'_pos : degree C A' > 0 := by
      rw [hdeg_A']
      have : 0 ≤ degree C A := by
        rw [CurveDivisor.degree_eq_sum]
        exact Finsupp.sum_nonneg (fun i _ => hA i)
      omega
    obtain ⟨f, hf⟩ := prescribed_poles_of_rational hF A' hA'_eff hdeg_A'_pos

    have hf_in_A' : (f : F) ∈ riemannRochSpace (F := F) (k := k) A' :=
      mem_riemannRochSpace_of_prescribed_poles hf

    have hf_not_in_A : (f : F) ∉ riemannRochSpace (F := F) (k := k) A := by
      intro hmem
      rw [mem_riemannRochSpace_iff] at hmem
      rcases hmem with hzero | ⟨hne, heff⟩
      · exact Units.ne_zero f hzero
      ·
        have hA'_P₀_pos : A' P₀ > 0 := by
          simp only [hA'_def, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
          linarith [hA P₀]
        have hord := hf.2 P₀ hA'_P₀_pos
        have heff_P₀ := heff P₀
        simp only [Finsupp.coe_add, Pi.add_apply] at heff_P₀
        rw [principalDivisor_apply] at heff_P₀
        have hmk0 : CurveWithOrd.ord (F := F) P₀ (Units.mk0 (↑f) hne) =
            CurveWithOrd.ord (F := F) P₀ f := by
          congr 1; exact Units.mk0_val f _
        rw [hmk0] at heff_P₀
        rw [hord] at heff_P₀
        simp only [hA'_def, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at heff_P₀
        omega


    have hstrict : riemannRochSpace (F := F) (k := k) A <
        riemannRochSpace (F := F) (k := k) A' :=
      lt_of_le_of_ne (riemannRochSpace_mono hAA')
        (fun h => hf_not_in_A (h ▸ hf_in_A'))

    have hfr_lt := Submodule.finrank_lt_finrank_of_lt hstrict

    have hfr_eq_AA' : (Module.finrank k (riemannRochSpace (F := F) (k := k) A') : ℤ) =
        (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) + 1 := by
      omega

    have hn' : (degree C B - degree C A').toNat = m := by
      rw [hdeg_A']; omega
    have hstep := ih hA'B hA'_eff hn'
    rw [hstep, hfr_eq_AA', hdeg_A']
    ring

/-- On a rational curve, for effective divisors $A \leq B$, $\dim_k L(B) = \dim_k L(A) + (\deg B - \deg A)$. -/
theorem riemannRochSpace_finrank_step_eq_of_rational
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (hF : F ≃ₐ[k] RatFunc k)
    {A B : CurveDivisor C} (hAB : A ≤ B) (hA : A.IsEffective)
    [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)] :
    (Module.finrank k (riemannRochSpace (F := F) (k := k) B) : ℤ) =
    (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) +
      (degree C B - degree C A) :=
  step_eq_aux hF _ hAB hA rfl

/-- On a rational curve, for any effective divisor $D$, the Riemann-Roch space satisfies $\dim_k L(D) \geq \deg D + 1$. -/
theorem riemannRochSpace_lower_bound_of_rational
    (hF : F ≃ₐ[k] RatFunc k)
    (D : CurveDivisor C) (hD : D.IsEffective) :
    degree C D + 1 ≤ (Module.finrank k (riemannRochSpace (F := F) (k := k) D) : ℤ) := by
  have h0D : (0 : CurveDivisor C) ≤ D := (CurveDivisor.isEffective_iff_nonneg D).mp hD
  haveI hfd0 := riemannRochSpace_zero_finiteDimensional (C := C) (F := F) (k := k)
  have hfr0 := riemannRochSpace_zero_finrank (C := C) (F := F) (k := k)
  have h0eff : (0 : CurveDivisor C).IsEffective := by
    intro P; simp [Finsupp.coe_zero]
  have hstep := riemannRochSpace_finrank_step_eq_of_rational (F := F) (k := k)
    hF h0D h0eff
  rw [hfr0, CurveDivisor.degree_zero, sub_zero] at hstep
  push_cast at hstep
  linarith

/-- Riemann-Roch on $\mathbb{P}^1$: for any effective divisor $D$ on a rational curve, $\ell(D) = \deg D + 1$. -/
theorem divisorDim_eq_degD_add_one_of_rational
    (hF : F ≃ₐ[k] RatFunc k)
    (D : CurveDivisor C) (hD : D.IsEffective) :
    (divisorDim (F := F) (k := k) D : ℤ) = degree C D + 1 := by

  have ⟨hfd, hub⟩ := riemannRochSpace_effective_dim_bound (F := F) (k := k) D hD
  haveI := hfd

  have hlb := riemannRochSpace_lower_bound_of_rational (F := F) (k := k) hF D hD

  rw [divisorDim_eq_finrank]
  linarith


end RiemannRochSpace
