/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

open NumberField Polynomial

noncomputable section

namespace DedekindCriterion

end DedekindCriterion

end

theorem DedekindCriterion.index_dvd_iff_span_eq_top
    {K : Type*} [Field K] [NumberField K]
    (α : RingOfIntegers K)
    (hK : Algebra.adjoin ℚ {(algebraMap (RingOfIntegers K) K) α} = ⊤)
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (u v w : ℤ[X])
    (hu_monic : u.Monic)
    (hv_monic : v.Monic)
    (huv_bar : Polynomial.map (Int.castRingHom (ZMod p)) u *
               Polynomial.map (Int.castRingHom (ZMod p)) v =
               Polynomial.map (Int.castRingHom (ZMod p)) (minpoly ℤ α))
    (husq : Squarefree (Polynomial.map (Int.castRingHom (ZMod p)) u))
    (hw : u * v - minpoly ℤ α = Polynomial.C (↑p : ℤ) * w) :
    (p ∣ (Algebra.adjoin ℤ ({α} : Set (RingOfIntegers K))).toSubmodule.toAddSubgroup.index) ↔
    (Ideal.span ({Polynomial.map (Int.castRingHom (ZMod p)) u,
                   Polynomial.map (Int.castRingHom (ZMod p)) v,
                   Polynomial.map (Int.castRingHom (ZMod p)) w} : Set ((ZMod p)[X])) = ⊤) := by sorry

noncomputable alias dedekind_criterion := DedekindCriterion.index_dvd_iff_span_eq_top
