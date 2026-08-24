/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HeckeKL

noncomputable section

universe u

variable {R : Type u} [Field R] [IsAlgClosed R] [CharZero R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

theorem kl_positivity_for_grothendieck_group
    (C : CoxeterGroupData) (y w : C.W) (n : ℕ) :
    0 ≤ (KazhdanLusztigPoly C y w).coeff n :=
  kazhdan_lusztig_conjecture_nonneg C y w n

theorem kl_multiplicity_in_grothendieck_group
    (C : CoxeterGroupData)
    (compat : CoxeterWeylCompatibility C rd wg)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hlam_dr : IsDominantRegularWeight rd wg lam)
    (y w : C.W) :
    (categoryO_multiplicity C rd wg compat lam y w : ℤ) =
      (KazhdanLusztigPoly C y w).eval 1 :=
  kazhdan_lusztig_conjecture_multiplicity C rd wg compat lam hlam_dr y w

end
