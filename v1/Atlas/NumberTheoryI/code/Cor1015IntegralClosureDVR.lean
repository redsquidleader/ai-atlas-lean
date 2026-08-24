/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.HenselFactorization

noncomputable section

open IsLocalRing

theorem integralClosure_isDVR
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [Algebra A E] [IsScalarTower A K E] :
    IsDiscreteValuationRing (integralClosure A E) :=
  integral_closure_complete_DVR_is_DVR A K E (integralClosure A E)

end
