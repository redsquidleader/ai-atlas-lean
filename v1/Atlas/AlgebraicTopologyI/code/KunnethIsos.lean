/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

open CategoryTheory

noncomputable section

namespace KunnethIsos

set_option checkBinderAnnotations false in
/-- **Tensor of quasi-isomorphisms is a quasi-isomorphism** (Section 25
helper for the Künneth theorem).  Over a principal ideal ring `R`, if
`f : C' ⟶ C` and `g : D' ⟶ D` are quasi-isomorphisms of chain complexes of
`R`-modules and the source complexes are degreewise free, then the induced
map `f ⊗ g : C' ⊗ D' ⟶ C ⊗ D` on tensor-product complexes is again a
quasi-isomorphism.  Freeness of the source ensures that tensoring preserves
homology, which is the key ingredient for the Künneth isomorphism in
algebraic topology. -/
theorem quasiIso_tensorHom
  {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
  {C' C D' D : ChainComplex (ModuleCat R) ℕ}
  (f : C' ⟶ C) (g : D' ⟶ D)
  [∀ n, Module.Free R (C'.X n)]
  [∀ n, Module.Free R (C.X n)]
  [HomologicalComplex.HasTensor C' D']
  [HomologicalComplex.HasTensor C D]
  [∀ i, (HomologicalComplex.tensorObj C' D').HasHomology i]
  [∀ i, (HomologicalComplex.tensorObj C D).HasHomology i]
  [∀ i, C'.HasHomology i] [∀ i, C.HasHomology i]
  [∀ i, D'.HasHomology i] [∀ i, D.HasHomology i]
  [QuasiIso f] [QuasiIso g] :
  QuasiIso (HomologicalComplex.tensorHom f g) := by sorry

end KunnethIsos

end
