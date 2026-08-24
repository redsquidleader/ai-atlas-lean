/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.ClassGroup

set_option maxHeartbeats 400000

namespace AbelJacobi

open WeierstrassCurve.Affine

/-- Abel-Jacobi surjectivity: every divisor class in `Pic⁰(W)` is represented by a point of the
elliptic curve `W`. Together with injectivity this gives the bijection `W ≅ Pic⁰(W)` (Thm 17.2,
Lec 17). -/
theorem abelJacobi_surjective
    (F : Type*) [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    Function.Surjective (Point.toClass : W.Point → Additive (ClassGroup W.CoordinateRing)) := by sorry

/-- Abel-Jacobi bijectivity for an elliptic curve `W`: the map sending a point to its divisor class
is a bijection `W.Point ≃ Pic⁰(W)` (Thm 17.2, Lec 17). -/
theorem abelJacobi_bijective
    (F : Type*) [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    Function.Bijective (Point.toClass : W.Point → Additive (ClassGroup W.CoordinateRing)) :=
  ⟨Point.toClass_injective, abelJacobi_surjective F W⟩

/-- Abel-Jacobi as an additive equivalence: for an elliptic curve `W` over `F`, the points form
an abelian group isomorphic to `Pic⁰(W) = ClassGroup W.CoordinateRing`. -/
noncomputable def abelJacobiEquiv
    (F : Type*) [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  AddEquiv.ofBijective Point.toClass (abelJacobi_bijective F W)

/-- The abelian group structure on the points of an elliptic curve obtained by transport along the
Abel-Jacobi equivalence with `Pic⁰(W)`. -/
@[reducible]
noncomputable def ellipticCurve_addCommGroup
    (F : Type*) [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    AddCommGroup W.Point :=
  (abelJacobiEquiv F W).toEquiv.addCommGroup

end AbelJacobi
