/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory

open CategoryTheory MonoidalCategory

universe u v w

/-- Proposition 1.48.2: A finite tensor category `C` is integral (i.e. its Frobenius–Perron
dimension function is integer-valued) if and only if it admits a quasi-fiber functor; this
is equivalent to `C` being the representation category of a finite-dimensional quasi-Hopf
algebra. -/
theorem Proposition_1_48_2
    (k : Type w) [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [EnoughProjectives C] [Linear k C] [RigidCategory C]
    (d : FPdimFunction (C := C)) :
    d.IsIntegral ↔ HasQuasiFiberFunctor k C :=
  integral_iff_hasQuasiFiberFunctor k d
