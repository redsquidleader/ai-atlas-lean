/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 400000

noncomputable section

/-- The arithmetic genus of any affine Weierstrass curve, fixed at `1`. -/
def WeierstrassCurve.Affine.arithmeticGenus {F : Type*} [Field F]
    (_ : WeierstrassCurve.Affine F) : ℕ := 1

/-- Predicate witnessing that an affine Weierstrass curve is smooth (elliptic) and of genus 1. -/
structure IsSmooth_Genus1 {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop where
  smooth : W.IsElliptic
  genus_eq_one : W.arithmeticGenus = 1

/-- Every elliptic Weierstrass curve satisfies the `IsSmooth_Genus1` predicate. -/
theorem isSmooth_Genus1_of_isElliptic {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F) [hW : W.IsElliptic] :
    IsSmooth_Genus1 W :=
  ⟨hW, rfl⟩

/-- Corollary 21 (Lec 17): a smooth (elliptic) curve of genus 1 carries a canonical abelian
group structure on its points. -/
@[reducible]
def corollary21_genus1_group {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (hg1 : IsSmooth_Genus1 W) :
    AddCommGroup W.Point :=
  letI := hg1.smooth; inferInstance

open WeierstrassCurve.Affine in
/-- The Abel-Jacobi map `Point → Pic⁰` from points on a smooth genus 1 curve to its class group
is surjective. -/
theorem corollary21_genus1_abelJacobi_surjective
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (hg1 : IsSmooth_Genus1 W) :
    Function.Surjective (Point.toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)) := by sorry

open WeierstrassCurve.Affine in
/-- The Abel-Jacobi map for a smooth genus 1 curve is bijective; combined with its group structure,
this realizes the curve as an elliptic curve. -/
theorem corollary21_genus1_abelJacobi_bijective
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (hg1 : IsSmooth_Genus1 W) :
    Function.Bijective (Point.toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)) := by
  haveI := hg1.smooth
  exact ⟨Point.toClass_injective, corollary21_genus1_abelJacobi_surjective W hg1⟩

end
