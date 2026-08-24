/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

set_option maxHeartbeats 1600000

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Hypercohomology

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
variable (D : Type*) [Category D] [Abelian D] [HasDerivedCategory D]

section Degreewise

variable (F : C ⥤ D) [F.Additive]

/-- Apply an additive functor `F : C ⥤ D` degreewise to a cochain complex,
producing the induced functor on cochain complexes. -/
def applyDegreewise : CochainComplex C ℤ ⥤ CochainComplex D ℤ :=
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Naive hypercohomology functor: apply `F` degreewise and then take homology in
degree `n`. Agrees with true hypercohomology only when `F` is exact or the input is
`F`-acyclic. -/
def naiveHypercohomologyFunctor (n : ℤ) : CochainComplex C ℤ ⥤ D :=
  applyDegreewise C D F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n

end Degreewise

section TotalDerived

variable (F : C ⥤ D) [F.Additive]

/-- The composite functor sending a cochain complex `K` in `C` to the image of `F(K)`
in the derived category of `D`. Its right derived functor is the source of hypercohomology. -/
def toDerivedOfD : CochainComplex C ℤ ⥤ DerivedCategory D :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- Existence of the total right derived functor of `F` along quasi-isomorphisms. -/
theorem totalDerivedExists :
  (toDerivedOfD C D F).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by sorry

/-- The total right derived functor `RF : D(C) ⥤ D(D)` of an additive functor `F`. -/
def totalDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D :=
  haveI := totalDerivedExists C D F
  (toDerivedOfD C D F).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

/-- The `n`-th hypercohomology functor `ℝ^n F` sending a complex `K` to the
`n`-th cohomology of `RF(K)`. -/
def hypercohomologyFunctor (n : ℤ) : CochainComplex C ℤ ⥤ D :=
  DerivedCategory.Q ⋙ totalDerivedFunctor C D F ⋙ DerivedCategory.homologyFunctor D n

/-- The `n`-th hypercohomology object `ℝ^n F (K)` of a complex `K`. -/
def hypercohomology (n : ℤ) (K : CochainComplex C ℤ) : D :=
  (hypercohomologyFunctor C D F n).obj K

end TotalDerived

section Compatibility

variable (F : C ⥤ D) [F.Additive]

/-- Hypercohomology of an object placed in a single degree agrees with the usual
right derived functor `R^n F (X)`. -/
noncomputable def hypercohomology_single_iso (X : C) (n : ℕ) :
  hypercohomology C D F (n : ℤ)
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X) ≅
    (F.rightDerived n).obj X := by sorry

end Compatibility

section SpectralSequence

variable (F : C ⥤ D) [F.Additive]

/-- The `E_2`-edge map of the hypercohomology spectral sequence
`R^p F (H^q K) ⟹ ℝ^{p+q} F (K)`. -/
noncomputable def spectralSequence_E2_map (K : CochainComplex C ℤ) (p : ℕ) (q : ℤ) :
  (F.rightDerived p).obj
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj K) ⟶
  hypercohomology C D F ((p : ℤ) + q) K := by sorry

/-- Naturality of the `E_2`-edge map of the hypercohomology spectral sequence. -/
theorem spectralSequence_E2_natural {K L : CochainComplex C ℤ} (f : K ⟶ L) (p : ℕ) (q : ℤ) :
  (F.rightDerived p).map
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).map f) ≫
    spectralSequence_E2_map C D F L p q =
  spectralSequence_E2_map C D F K p q ≫
    (hypercohomologyFunctor C D F ((p : ℤ) + q)).map f := by sorry

/-- Spectral sequence degeneration: if every term `K.X i` is `F`-acyclic, then
hypercohomology coincides with the naive degreewise version. -/
noncomputable def acyclic_degeneration (K : CochainComplex C ℤ)
    (hacyclic : ∀ (i : ℤ) (p : ℕ) (_ : 0 < p),
      IsZero ((F.rightDerived p).obj (K.X i)))
    (n : ℤ) :
  hypercohomology C D F n K ≅ (naiveHypercohomologyFunctor C D F n).obj K := by sorry

end SpectralSequence

end Hypercohomology

end
