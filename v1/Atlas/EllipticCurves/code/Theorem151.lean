/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.WeierstrassP
import Atlas.EllipticCurves.code.Uniformization
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open Complex

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The Weierstrass curve `E_L : y^2 = 4x^3 - g₂(L)·x - g₃(L)` associated to a
lattice `L`, presented in long Weierstrass form with coefficients
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, -g₂/4, -g₃/4)`. -/
def ellipticCurveEL : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(L.g₂ / 4), -(L.g₃ / 4)⟩

/-- The affine model of `ellipticCurveEL L`, used to talk about its affine
`Point` type. -/
def ellipticCurveEL_affine : WeierstrassCurve.Affine ℂ :=
  L.ellipticCurveEL.toAffine

/-- The type of points on the elliptic curve `E_L` associated to the lattice `L`. -/
abbrev ELPoint : Type := L.ellipticCurveEL_affine.Point

/-- The additive group structure on `E_L(ℂ)` from the chord-tangent law on a
Weierstrass curve. -/
instance : AddCommGroup L.ELPoint := by
  classical
  exact WeierstrassCurve.Affine.Point.instAddCommGroup

/-- The discriminant of the affine elliptic curve `E_L` equals the lattice
discriminant `Δ(L) = g₂³ - 27 g₃²` (up to the normalization built into
`discriminantLattice`). -/
lemma ellipticCurveEL_Δ_eq : L.ellipticCurveEL_affine.Δ = L.discriminantLattice := by
  unfold discriminantLattice ellipticCurveEL_affine ellipticCurveEL WeierstrassCurve.toAffine
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The discriminant of `E_L` is nonzero, so `E_L` really is an elliptic curve
(this is Lemma 14.33 applied to `E_L`). -/
lemma ellipticCurveEL_Δ_ne_zero : L.ellipticCurveEL_affine.Δ ≠ 0 := by
  rw [L.ellipticCurveEL_Δ_eq]
  exact L.discriminantLattice_ne_zero

/-- For any non-lattice point `z`, the pair `(℘(z), ℘'(z)/2)` satisfies the
Weierstrass equation of `E_L`, i.e. lies on the affine curve. This is the
key calculation behind the uniformization map of Theorem 15.1. -/
lemma weierstrassP_point_equation (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) :
    L.ellipticCurveEL_affine.Equation
      (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ellipticCurveEL_affine, ellipticCurveEL, WeierstrassCurve.toAffine]
  have h := L.weierstrassPFun_differentialEquation z hz
  simp only [g₂Fun_eq, g₃Fun_eq] at h

  simp only [zero_mul, add_zero]
  rw [div_pow, h]
  field_simp
  ring

/-- For any non-lattice point `z`, the point `(℘(z), ℘'(z)/2)` is a
nonsingular point of `E_L`, since `E_L` has nonzero discriminant. -/
theorem weierstrassP_point_nonsingular (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) :
    L.ellipticCurveEL_affine.Nonsingular
      (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2) := by
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (L.ellipticCurveEL_Δ_ne_zero)).mp (L.weierstrassP_point_equation z hz)

/-- The uniformization map on a non-lattice point: send `z ∉ L` to the affine
point `(℘(z), ℘'(z)/2)` of `E_L`. -/
def PhiAux (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) : L.ELPoint :=
  WeierstrassCurve.Affine.Point.some
    (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2)
    (L.weierstrassP_point_nonsingular z hz)

/-- The complex torus `ℂ / L` for the lattice `L`. -/
abbrev complexTorus : Type := ℂ ⧸ L.toAddSubgroup

/-- The complex torus inherits the additive group structure from the quotient
of `ℂ` by `L`. -/
instance : AddCommGroup L.complexTorus :=
  QuotientAddGroup.Quotient.addCommGroup L.toAddSubgroup

/-- The set-theoretic uniformization lift `ℂ → E_L(ℂ)` underlying `Φ`: lattice
points are sent to the identity, and any other `z` to `(℘(z), ℘'(z)/2)`. -/
def PhiLift (z : ℂ) : L.ELPoint := by
  classical
  exact if hz : z ∈ (L.lattice : Set ℂ) then 0
    else L.PhiAux z hz

/-- The lift `PhiLift` is `L`-periodic: shifting `z` by a lattice element does
not change its image, which is what allows it to descend to `ℂ / L`. -/
lemma PhiLift_add_lattice (z ω : ℂ) (hω : ω ∈ L.lattice) :
    L.PhiLift (z + ω) = L.PhiLift z := by
  classical
  unfold PhiLift
  by_cases hz : z ∈ (L.lattice : Set ℂ)
  ·
    have hzw : z + ω ∈ (L.lattice : Set ℂ) :=
      L.lattice.add_mem hz hω
    simp [hzw, hz]
  ·
    by_cases hzw : z + ω ∈ (L.lattice : Set ℂ)
    ·
      exfalso
      apply hz
      have : z = (z + ω) - ω := by ring
      rw [this]
      exact L.lattice.sub_mem hzw hω
    · simp only [hzw, hz, dite_false]
      unfold PhiAux
      congr 1
      · exact L.weierstrassPFun_add_lattice z ω hω
      · rw [L.derivWeierstrassPFun_add_lattice z ω hω]

/-- The uniformization map `Φ : ℂ/L → E_L(ℂ)` as a function, obtained by
descending `PhiLift` to the quotient using its `L`-periodicity. -/
def PhiFun : L.complexTorus → L.ELPoint :=
  Quot.lift (L.PhiLift) <| by
    intro a b hab
    have hab' := hab
    change (QuotientAddGroup.leftRel L.toAddSubgroup).r a b at hab'
    rw [QuotientAddGroup.leftRel_apply] at hab'

    have hω : -a + b ∈ (L.lattice : Set ℂ) := hab'
    have : b = a + (-a + b) := by ring
    rw [this]
    exact (L.PhiLift_add_lattice a (-a + b) hω).symm

/-- The uniformization map sends the identity of `ℂ/L` (the class of `0`) to
the identity (point at infinity) of `E_L`. -/
lemma PhiFun_zero : L.PhiFun 0 = 0 := by
  classical
  show L.PhiLift 0 = 0
  unfold PhiLift
  have h0 : (0 : ℂ) ∈ (L.lattice : Set ℂ) := L.lattice.zero_mem
  simp [h0]

/-- Computational rule for `PhiFun`: on the class of a non-lattice point `z`,
the map agrees with `PhiAux z`, i.e. evaluates to `(℘(z), ℘'(z)/2)`. -/
lemma PhiFun_mk (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) :
    L.PhiFun (QuotientAddGroup.mk z) = L.PhiAux z hz := by
  classical
  show L.PhiLift z = L.PhiAux z hz
  unfold PhiLift
  simp [hz]

/-- Additivity of the uniformization map: `Φ(a + b) = Φ(a) + Φ(b)` on the
complex torus. This is the group-homomorphism content of Theorem 15.1, the
classical addition law for the Weierstrass `℘` function. -/
theorem PhiFun_map_add (a b : L.complexTorus) :
    L.PhiFun (a + b) = L.PhiFun a + L.PhiFun b := by sorry

/-- The uniformization map `Φ : ℂ/L → E_L(ℂ)` packaged as a group
homomorphism, using `PhiFun_zero` and `PhiFun_map_add`. -/
def complexTorusToEL : L.complexTorus →+ L.ELPoint where
  toFun := L.PhiFun
  map_zero' := L.PhiFun_zero
  map_add' := L.PhiFun_map_add

/-- Injectivity of `Φ`: relying on the parity/duplication properties of `℘`
and `℘'`, two torus classes mapping to the same point of `E_L` must agree.
This is the injectivity half of Theorem 15.1. -/
theorem Phi_injective : Function.Injective L.complexTorusToEL := by
  intro a b hab

  have hab' := hab

  revert hab hab'
  refine Quot.inductionOn a fun z₁ => Quot.inductionOn b fun z₂ hab hab' => ?_


  apply Quot.sound
  change (QuotientAddGroup.leftRel L.toAddSubgroup).r z₁ z₂
  rw [QuotientAddGroup.leftRel_apply]

  change L.PhiFun (QuotientAddGroup.mk z₁) = L.PhiFun (QuotientAddGroup.mk z₂) at hab
  classical
  by_cases hz₁ : z₁ ∈ (L.lattice : Set ℂ) <;> by_cases hz₂ : z₂ ∈ (L.lattice : Set ℂ)
  ·
    exact L.lattice.add_mem (L.lattice.neg_mem hz₁) hz₂
  ·
    exfalso
    have h1 : L.PhiFun (QuotientAddGroup.mk z₁) = 0 := by
      show L.PhiLift z₁ = 0; unfold PhiLift; simp [hz₁]
    rw [h1, L.PhiFun_mk z₂ hz₂] at hab
    exact absurd hab.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
  ·
    exfalso
    have h2 : L.PhiFun (QuotientAddGroup.mk z₂) = 0 := by
      show L.PhiLift z₂ = 0; unfold PhiLift; simp [hz₂]
    rw [h2, L.PhiFun_mk z₁ hz₁] at hab
    exact absurd hab (WeierstrassCurve.Affine.Point.some_ne_zero _)
  ·
    rw [L.PhiFun_mk z₁ hz₁, L.PhiFun_mk z₂ hz₂] at hab

    simp only [PhiAux, WeierstrassCurve.Affine.Point.some.injEq] at hab
    obtain ⟨h℘, h℘'_div⟩ := hab

    have h℘' : L.derivWeierstrassPFun z₁ = L.derivWeierstrassPFun z₂ := by
      field_simp at h℘'_div; exact h℘'_div

    rcases L.weierstrassP_eq_implies_pm z₁ z₂ hz₁ hz₂ h℘ with hdiff | hsum
    ·
      have : -z₁ + z₂ = -(z₁ - z₂) := by ring
      rw [this]; exact L.lattice.neg_mem hdiff
    ·
      have h_neg : L.derivWeierstrassPFun z₂ = -L.derivWeierstrassPFun z₁ := by
        have hp := L.derivWeierstrassPFun_add_lattice (-z₁) (z₁ + z₂) hsum
        simp only [show -z₁ + (z₁ + z₂) = z₂ from by ring] at hp
        rw [hp, L.derivWeierstrassPFun_odd]

      have h_zero : L.derivWeierstrassPFun z₁ = 0 := by
        have h2 : (2 : ℂ) * L.derivWeierstrassPFun z₁ = 0 := by linear_combination h℘' + h_neg
        exact (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

      have h2z₁ : (2 : ℂ) * z₁ ∈ (L.lattice : Set ℂ) :=
        (L.derivWeierstrassPFun_eq_zero_iff z₁ hz₁).mp h_zero

      have : -z₁ + z₂ = -((2 : ℂ) * z₁ - (z₁ + z₂)) := by ring
      rw [this]
      exact L.lattice.neg_mem (L.lattice.sub_mem h2z₁ hsum)

/-- Surjectivity of `Φ`: every point of `E_L(ℂ)` is the image of some torus
class. This is the surjectivity half of Theorem 15.1. -/
theorem Phi_surjective : Function.Surjective L.complexTorusToEL := by sorry

/-- The uniformization map `Φ : ℂ/L → E_L(ℂ)` is bijective, combining
injectivity and surjectivity. -/
theorem Phi_bijective : Function.Bijective L.complexTorusToEL :=
  ⟨L.Phi_injective, L.Phi_surjective⟩

/-- Theorem 15.1: the map `Φ : ℂ/L → E_L(ℂ)` is a group isomorphism between
the complex torus and the complex points of the elliptic curve `E_L`. -/
def uniformization_iso : L.complexTorus ≃+ L.ELPoint :=
  AddEquiv.ofBijective L.complexTorusToEL L.Phi_bijective

end ComplexLattice

end
