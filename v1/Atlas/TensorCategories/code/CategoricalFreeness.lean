/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w

namespace CategoryTheory

/-- A surjective quasi-tensor functor between abelian monoidal categories: here packaged as
the underlying functor `F : C ⥤ D`. Used as a stand-in for the data of a quasi-tensor
functor along with the surjectivity hypothesis of Definition 1.49.1. -/
structure SurjectiveQuasiTensorFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D

/-- A Frobenius-Perron dimension function `fpDim : C → ℝ` on a monoidal category,
normalized so that `fpDim (𝟙_ C) = 1`, taking positive values, multiplicative on tensor
products and invariant under isomorphisms. -/
structure FPdimFunction {C : Type u} [Category.{v} C] [MonoidalCategory C] where
  fpDim : C → ℝ
  fpDim_unit : fpDim (𝟙_ C) = 1
  fpDim_pos : ∀ (X : C), fpDim X > 0
  fpDim_tensor : ∀ (X Y : C), fpDim (X ⊗ Y) = fpDim X * fpDim Y
  fpDim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → fpDim X = fpDim Y

namespace FPdimFunction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A Frobenius-Perron dimension function is integral (Definition 1.48.1) if the dimension
of every object is an integer. -/
def IsIntegral (d : FPdimFunction (C := C)) : Prop :=
  ∀ (X : C), ∃ (n : ℤ), d.fpDim X = ↑n

end FPdimFunction

/-- Combinatorial data describing the simple/projective decomposition of a finite
multitensor category: a finite indexing type `I`, simple objects `simpleObj i`, projective
covers `projCover i`, multiplicities of `projCover` in arbitrary objects, and the
distinguished index for the unit object. -/
class FiniteMultitensorDecompData (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] where
  I : Type*
  [instFintype : Fintype I]
  [instDecEq : DecidableEq I]
  simpleObj : I → C
  projCover : I → C
  projDecompMult : C → I → ℕ
  unitIdx : I
  simpleObj_unitIdx : Nonempty (simpleObj unitIdx ≅ 𝟙_ C)

attribute [reducible, instance] FiniteMultitensorDecompData.instFintype
  FiniteMultitensorDecompData.instDecEq

/-- The Frobenius-Perron dimension `FPdim(C)` of a finite tensor category
(Definition 1.47.5): `Σ FPdim(X_i) FPdim(P_i)` summed over simple objects `X_i` and their
projective covers `P_i`. -/
noncomputable def categoricalFPdim
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    (decomp : FiniteMultitensorDecompData k C)
    (d : FPdimFunction (C := C)) : ℝ :=
  ∑ i : decomp.I, d.fpDim (decomp.simpleObj i) * d.fpDim (decomp.projCover i)

/-- The coefficient `[F(R_C) : X_j]` of the simple object `X_j` of `D` in the image of the
regular object `R_C` under the functor `F`, expressed via the simple/projective
decomposition data of `C`. -/
noncomputable def coeffF_RC
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (j : decompD.I) : ℝ :=
  ∑ i : decompC.I,
    dC.fpDim (decompC.simpleObj i) *
      (decompD.projDecompMult (QTF.F.obj (decompC.projCover i)) j : ℝ)

/-- Theorem 1.50.1: For a surjective quasi-tensor functor `F : C → D`, the image of the
regular object is `F(R_C) = (FPdim(C)/FPdim(D)) R_D`, expressed coefficient-wise on simple
objects. -/
theorem thm_1_50_1
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    ∀ j : decompD.I,
      coeffF_RC QTF decompC decompD dC j =
        (categoricalFPdim decompC dC / categoricalFPdim decompD dD) *
          dD.fpDim (decompD.simpleObj j) := by
  sorry

/-- Theorem 1.50.1 (named restatement): The relation `coeffF_RC = (FPdim C / FPdim D) ·
FPdim(X_j)` for surjective quasi-tensor functors. -/
theorem theorem_1_50_1
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    ∀ j : decompD.I,
      coeffF_RC QTF decompC decompD dC j =
        (categoricalFPdim decompC dC / categoricalFPdim decompD dD) *
          dD.fpDim (decompD.simpleObj j) := by
  exact thm_1_50_1 QTF decompC decompD dC dD hC_pos hD_pos

/-- Sum `Σ FPdim(X_i) dim Hom(F(P_i), 𝟙_D)` appearing in Corollary 1.50.2, which is shown
to equal the ratio `FPdim(C)/FPdim(D)`. -/
noncomputable def homDimSum
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (dC : FPdimFunction (C := C)) : ℝ :=
  ∑ i : decompC.I,
    dC.fpDim (decompC.simpleObj i) *
      (Module.finrank k (QTF.F.obj (decompC.projCover i) ⟶ 𝟙_ D) : ℝ)

/-- Corollary 1.50.2 (formula part): `FPdim(C)/FPdim(D) = Σ FPdim(X_i) dim Hom(F(P_i),
𝟙_D)`. -/
theorem cor_1_50_2_formula
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    categoricalFPdim decompC dC / categoricalFPdim decompD dD =
      homDimSum QTF decompC dC := by
  sorry

/-- The hom-dimension sum used in Corollary 1.50.2 is always at least `1`, since the trivial
contribution from the unit projective already yields `1`. -/
theorem homDimSum_ge_one
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (dC : FPdimFunction (C := C)) :
    homDimSum QTF decompC dC ≥ 1 := by sorry

/-- Corollary 1.50.2 (algebraic integrality): the ratio `FPdim(C)/FPdim(D)` is an algebraic
integer (here recorded as an integer over `ℤ` in `ℝ`). -/
theorem cor_1_50_2_part2_algebraic_integer
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    IsIntegral ℤ (categoricalFPdim decompC dC / categoricalFPdim decompD dD) := by
  sorry

/-- Corollary 1.50.2 (full statement): `FPdim(C) ≥ FPdim(D)`, the ratio `FPdim(C)/FPdim(D)`
is an algebraic integer, and equals the hom-dimension sum `Σ FPdim(X_i) dim
Hom(F(P_i), 𝟙_D)`. -/
theorem corollary_1_50_2
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :

    categoricalFPdim decompC dC ≥ categoricalFPdim decompD dD ∧

    IsIntegral ℤ (categoricalFPdim decompC dC / categoricalFPdim decompD dD) ∧

    categoricalFPdim decompC dC / categoricalFPdim decompD dD =
      homDimSum QTF decompC dC := by
  refine ⟨?_, cor_1_50_2_part2_algebraic_integer QTF decompC decompD dC dD hC_pos hD_pos,
    cor_1_50_2_formula QTF decompC decompD dC dD hC_pos hD_pos⟩

  have h_ratio_ge_one :
      categoricalFPdim decompC dC / categoricalFPdim decompD dD ≥ 1 := by
    rw [cor_1_50_2_formula QTF decompC decompD dC dD hC_pos hD_pos]
    exact homDimSum_ge_one QTF decompC dC
  rwa [ge_iff_le, le_div_iff₀ hD_pos, one_mul] at h_ratio_ge_one

/-- Corollary 1.50.2 (inequality part): `FPdim(C) ≥ FPdim(D)` for a surjective quasi-tensor
functor `F : C → D`. -/
theorem cor_1_50_2_part1
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    categoricalFPdim decompC dC ≥ categoricalFPdim decompD dD := by
  have h_ratio_ge_one :
      categoricalFPdim decompC dC / categoricalFPdim decompD dD ≥ 1 := by
    rw [cor_1_50_2_formula QTF decompC decompD dC dD hC_pos hD_pos]
    exact homDimSum_ge_one QTF decompC dC
  rwa [ge_iff_le, le_div_iff₀ hD_pos, one_mul] at h_ratio_ge_one

/-- The ratio `FPdim(C) / FPdim(D)` is at least `1` for a surjective quasi-tensor functor
from `C` to `D`. -/
theorem fpDimRatio_ge_one
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    categoricalFPdim decompC dC / categoricalFPdim decompD dD ≥ 1 := by
  rw [ge_iff_le, one_le_div₀ hD_pos]
  exact cor_1_50_2_part1 QTF decompC decompD dC dD hC_pos hD_pos

/-- Witness form of the divisibility part of Corollary 1.50.2: there is an algebraic
integer `q ≥ 1` with `FPdim(C) = q · FPdim(D)`. -/
theorem cor_1_50_2_fpDim_dvd
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    ∃ (q : ℝ), q ≥ 1 ∧
      IsIntegral ℤ q ∧
      categoricalFPdim decompC dC = q * categoricalFPdim decompD dD := by
  refine ⟨categoricalFPdim decompC dC / categoricalFPdim decompD dD,
    fpDimRatio_ge_one QTF decompC decompD dC dD hC_pos hD_pos,
    cor_1_50_2_part2_algebraic_integer QTF decompC decompD dC dD hC_pos hD_pos,
    ?_⟩
  rw [div_mul_cancel₀]
  exact ne_of_gt hD_pos

/-- Existence form of divisibility: there exists an algebraic integer `α` with
`FPdim(C) = α · FPdim(D)`. -/
theorem cor_1_50_2_divisibility
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0) :
    ∃ (α : ℝ), IsIntegral ℤ α ∧
      categoricalFPdim decompC dC = α * categoricalFPdim decompD dD := by
  have h_int := cor_1_50_2_part2_algebraic_integer QTF decompC decompD dC dD hC_pos hD_pos
  exact ⟨categoricalFPdim decompC dC / categoricalFPdim decompD dD, h_int,
    (div_mul_cancel₀ _ (ne_of_gt hD_pos)).symm⟩

/-- Corollary 1.50.3 (integrality transport): if `C` is integral and `F : C → D` is a
surjective quasi-tensor functor, then `D` is also integral. -/
theorem integral_of_surjective_quasi_tensor
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_int : dC.IsIntegral) :
    dD.IsIntegral := by
  sorry

/-- When the FP-dimension function on `C` is integral, the hom-dimension sum is a positive
natural number. -/
theorem homDimSum_isNat_of_integral
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (dC : FPdimFunction (C := C))
    (hC_int : dC.IsIntegral) :
    ∃ (m : ℕ), 0 < m ∧ homDimSum QTF decompC dC = ↑m := by

  have hf_nat : ∀ i : decompC.I, ∃ (m : ℕ),
      dC.fpDim (decompC.simpleObj i) = (m : ℝ) := by
    intro i
    obtain ⟨n, hn⟩ := hC_int (decompC.simpleObj i)
    have hpos : (0 : ℤ) < n := by exact_mod_cast hn ▸ dC.fpDim_pos (decompC.simpleObj i)
    exact ⟨n.toNat, by rw [hn]; congr 1; exact (Int.toNat_of_nonneg (le_of_lt hpos)).symm⟩
  choose mf hmf using hf_nat

  have hsum : homDimSum QTF decompC dC =
      ((∑ i : decompC.I,
        mf i * Module.finrank k (QTF.F.obj (decompC.projCover i) ⟶ 𝟙_ D) : ℕ) : ℝ) := by
    simp only [homDimSum]
    push_cast
    congr 1
    ext i
    rw [hmf i]
  have hge := homDimSum_ge_one QTF decompC dC
  rw [hsum] at hge ⊢
  exact ⟨_, by exact_mod_cast hge, rfl⟩

/-- If the FP-dimension function `d` on a finite tensor category `C` is integral and the
categorical FP-dimension is positive, then `FPdim(C)` is a positive natural number. -/
theorem categoricalFPdim_isNat_of_integral
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    (decomp : FiniteMultitensorDecompData k C)
    (d : FPdimFunction (C := C))
    (hd : d.IsIntegral)
    (hpos : categoricalFPdim decomp d > 0) :
    ∃ (n : ℕ), 0 < n ∧ categoricalFPdim decomp d = ↑n := by
  sorry

/-- Corollary 1.50.3 (freeness of `F(R_C)`): under integrality of `C`, the ratio
`FPdim(C)/FPdim(D)` is a positive integer, the rank of `F(R_C)` as a free `R_D`-module. -/
theorem fRC_free_of_integral
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0)
    (hC_int : dC.IsIntegral) :
    ∃ (n : ℕ), n > 0 ∧
      categoricalFPdim decompC dC / categoricalFPdim decompD dD = ↑n := by
  obtain ⟨m, hm_pos, hm_eq⟩ := homDimSum_isNat_of_integral QTF decompC dC hC_int
  exact ⟨m, hm_pos,
    (cor_1_50_2_formula QTF decompC decompD dC dD hC_pos hD_pos).trans hm_eq⟩

/-- Coefficient form of the freeness statement: under integrality, the coefficients
`[F(R_C) : X_j]` are all equal to `n · FPdim(X_j)` for a common positive integer `n`. -/
theorem fRC_free_coefficients_of_integral
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0)
    (hC_int : dC.IsIntegral) :
    ∃ (n : ℕ), n > 0 ∧
      (∀ j : decompD.I,
        coeffF_RC QTF decompC decompD dC j = ↑n * dD.fpDim (decompD.simpleObj j)) := by
  obtain ⟨n, hn_pos, hn_eq⟩ := fRC_free_of_integral QTF decompC decompD dC dD hC_pos hD_pos hC_int
  exact ⟨n, hn_pos, fun j => by
    have h1501 := thm_1_50_1 QTF decompC decompD dC dD hC_pos hD_pos j
    rw [h1501, hn_eq]⟩

/-- Integral divisibility form of Corollary 1.50.3: there are positive integers `nC`, `nD`,
`m` with `FPdim(C) = nC`, `FPdim(D) = nD` and `nD · m = nC`. -/
theorem fpDim_dvd_of_integral
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0)
    (hC_int : dC.IsIntegral) :
    ∃ (nC nD m : ℕ),
      categoricalFPdim decompC dC = ↑nC ∧
      categoricalFPdim decompD dD = ↑nD ∧
      nD * m = nC ∧ 0 < nD ∧ 0 < m := by
  have hD_int :=
    integral_of_surjective_quasi_tensor QTF decompC decompD dC dD hC_int
  obtain ⟨nC, hnC_pos, hnC_eq⟩ :=
    categoricalFPdim_isNat_of_integral decompC dC hC_int hC_pos
  obtain ⟨nD, hnD_pos, hnD_eq⟩ :=
    categoricalFPdim_isNat_of_integral decompD dD hD_int hD_pos
  obtain ⟨m, hm_pos, hm_eq⟩ :=
    fRC_free_of_integral QTF decompC decompD dC dD hC_pos hD_pos hC_int
  refine ⟨nC, nD, m, hnC_eq, hnD_eq, ?_, hnD_pos, hm_pos⟩
  rw [hnC_eq, hnD_eq] at hm_eq
  have hD_ne : (nD : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hnD_pos)
  rw [div_eq_iff hD_ne] at hm_eq
  have : (nC : ℝ) = (nD * m : ℕ) := by push_cast; linarith
  exact_mod_cast this.symm

/-- Corollary 1.50.3 (full statement): If `C` is integral and `F : C → D` is a surjective
quasi-tensor functor, then `D` is integral, the ratio `FPdim(C)/FPdim(D)` is a positive
integer, `F(R_C)` is free over `R_D` of that rank, and `FPdim(D)` divides `FPdim(C)` as
integers. -/
theorem corollary_1_50_3
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0)
    (hC_int : dC.IsIntegral) :

    dD.IsIntegral ∧

    (∃ (n : ℕ), n > 0 ∧
      categoricalFPdim decompC dC / categoricalFPdim decompD dD = ↑n) ∧

    (∃ (n : ℕ), n > 0 ∧
      ∀ j : decompD.I,
        coeffF_RC QTF decompC decompD dC j = ↑n * dD.fpDim (decompD.simpleObj j)) ∧

    (∃ (nC nD m : ℕ),
      categoricalFPdim decompC dC = ↑nC ∧
      categoricalFPdim decompD dD = ↑nD ∧
      nD * m = nC ∧ 0 < nD ∧ 0 < m) := by
  exact ⟨integral_of_surjective_quasi_tensor QTF decompC decompD dC dD hC_int,
    fRC_free_of_integral QTF decompC decompD dC dD hC_pos hD_pos hC_int,
    fRC_free_coefficients_of_integral QTF decompC decompD dC dD hC_pos hD_pos hC_int,
    fpDim_dvd_of_integral QTF decompC decompD dC dD hC_pos hD_pos hC_int⟩

end CategoryTheory
