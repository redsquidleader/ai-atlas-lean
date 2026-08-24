/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.DirectSum.Basic

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace ProjectiveQCohProperties

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A `ℤ`-graded module over a `ℕ`-graded ring `𝒜`: an `A`-module with a `ℤ`-indexed
internal direct sum decomposition compatible with the grading on `𝒜`. -/
structure ZGradedModule where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module A carrier]
  component : ℤ → AddSubgroup carrier
  isInternal : DirectSum.IsInternal component
  graded_smul : ∀ (n : ℕ) (d : ℤ) (a : A) (m : carrier),
    a ∈ (𝒜 n : Set A) → m ∈ component d → a • m ∈ component (↑n + d)

attribute [instance] ZGradedModule.instAddCommGroup ZGradedModule.instModule

namespace ZGradedModule

variable {𝒜}

/-- A graded module is finitely generated if its underlying module is. -/
def IsFG (M : ZGradedModule 𝒜) : Prop :=
  Module.Finite A M.carrier

/-- A graded module is "finite-dimensional" if only finitely many graded components
are nonzero. -/
def IsFinDim (M : ZGradedModule 𝒜) : Prop :=
  ∃ (S : Finset ℤ), ∀ d, d ∉ S → M.component d = ⊥

/-- A graded module is locally nilpotent (with respect to the irrelevant ideal) if for
every element `x`, some power of every element of the irrelevant ideal annihilates `x`. -/
def IsLocNilpotent (M : ZGradedModule 𝒜) : Prop :=
  ∀ (x : M.carrier), ∃ (d : ℕ),
    ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal → a ^ d • x = 0

/-- A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of graded modules. -/
structure SES (M₁ M₂ M₃ : ZGradedModule 𝒜) where
  f : M₁.carrier →ₗ[A] M₂.carrier
  g : M₂.carrier →ₗ[A] M₃.carrier
  f_injective : Function.Injective f
  g_surjective : Function.Surjective g
  exact : LinearMap.ker g = LinearMap.range f

end ZGradedModule

/-- The grading shift `A(d)`: `A` viewed as a graded module with degrees shifted by `d`. -/
noncomputable def ZGradedModule.gradeShift
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ) : ZGradedModule 𝒜 := by sorry

/-- The direct sum of `k` copies of a graded module `M`. -/
noncomputable def ZGradedModule.copies
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (M : ZGradedModule 𝒜) (k : ℕ) : ZGradedModule 𝒜 := by sorry

/-- Predicate that a sheaf of modules on a scheme is quasicoherent. -/
def IsQCoh {X : Scheme.{u}} (ℱ : X.Modules) : Prop :=
  ℱ.IsQuasicoherent

/-- Placeholder predicate "is coherent" for a sheaf of modules on a scheme. -/
noncomputable def CoherentSheafPred : {X : Scheme.{u}} → X.Modules → Prop := by sorry

/-- The "tilde" construction sending a graded `𝒜`-module to the associated
quasicoherent sheaf on `Proj 𝒜`. -/
noncomputable def tildeProjFunctor (M : ZGradedModule 𝒜) : (Proj 𝒜).Modules := by sorry

/-- The Serre twisting sheaf `𝒪(d)` on `Proj 𝒜`. -/
noncomputable def twistingSheaf (d : ℤ) : (Proj 𝒜).Modules := by sorry

/-- The tilde of `k` copies of the shifted graded ring `A(-d)` is canonically isomorphic
to a coproduct of `k` copies of `𝒪(-d)`. -/
noncomputable def tilde_shifted_copies_iso_coproduct_twisting (d : ℕ) (k : ℕ) :
    tildeProjFunctor 𝒜 ((ZGradedModule.gradeShift 𝒜 (-↑d)).copies k) ≅
      (∐ fun (_ : Fin k) => twistingSheaf 𝒜 (-(d : ℤ))) := by sorry

/-- Recovers a graded module from a sheaf on `Proj 𝒜` by taking the direct sum of
twisted global sections `⊕ Γ(F(n))`. -/
noncomputable def gradedModuleOfSheaf (ℱ : (Proj 𝒜).Modules) : ZGradedModule 𝒜 := by sorry

/-- Proposition 20 (exactness): the `M ↦ M̃` functor sends short exact sequences of
graded modules to short exact sequences of sheaves on `Proj 𝒜`. -/
theorem prop20_tildeFunctor_exact
    (M₁ M₂ M₃ : ZGradedModule 𝒜)
    (ses : ZGradedModule.SES M₁ M₂ M₃) :
    ∃ (f : tildeProjFunctor 𝒜 M₁ ⟶ tildeProjFunctor 𝒜 M₂)
      (g : tildeProjFunctor 𝒜 M₂ ⟶ tildeProjFunctor 𝒜 M₃)
      (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact := by sorry

/-- Proposition 20 (essential surjectivity): every quasicoherent sheaf on `Proj 𝒜` is
isomorphic to `M̃` for some graded module `M`. -/
theorem prop20_tildeFunctor_essentiallySurjective
    (ℱ : (Proj 𝒜).Modules)
    (hqc : IsQCoh ℱ) :
    ∃ (M : ZGradedModule 𝒜), Nonempty (tildeProjFunctor 𝒜 M ≅ ℱ) := by sorry

/-- Refinement of Proposition 20: every coherent sheaf on `Proj 𝒜` comes from a
finitely generated graded module. -/
theorem prop20_tildeFunctor_essentiallySurjective_fg
    (ℱ : (Proj 𝒜).Modules)
    (hcoh : CoherentSheafPred ℱ) :
    ∃ (M : ZGradedModule 𝒜), M.IsFG ∧
      Nonempty (tildeProjFunctor 𝒜 M ≅ ℱ) := by sorry

/-- Every finitely generated graded module is a quotient of a finite direct sum of
shifted copies of the graded ring `A(-d)`. -/
theorem fg_graded_surjection_from_shifted_free
    (M : ZGradedModule 𝒜) (hfg : M.IsFG) :
    ∃ (d : ℕ) (k : ℕ)
      (f : ((ZGradedModule.gradeShift 𝒜 (-↑d)).copies k).carrier →ₗ[A] M.carrier),
      Function.Surjective f := by sorry

/-- A surjection of graded modules induces an epimorphism between their tilde sheaves. -/
theorem tildeProjFunctor_epi_of_surjection
    (M N : ZGradedModule 𝒜) (f : M.carrier →ₗ[A] N.carrier)
    (hf : Function.Surjective f) :
    ∃ (φ : tildeProjFunctor 𝒜 M ⟶ tildeProjFunctor 𝒜 N), Epi φ := by sorry

/-- Corollary 18 (module-level): every coherent sheaf on `Proj 𝒜` admits a surjection
from the tilde of `k` copies of `A(-d)`. -/
theorem cor18_coherent_quotient_module_level
    (ℱ : (Proj 𝒜).Modules)
    (hcoh : CoherentSheafPred ℱ) :
    ∃ (d : ℕ) (k : ℕ),
      ∃ (φ : tildeProjFunctor 𝒜 ((ZGradedModule.gradeShift 𝒜 (-↑d)).copies k) ⟶ ℱ),
        Epi φ := by

  obtain ⟨M, hfg, ⟨iso⟩⟩ := prop20_tildeFunctor_essentiallySurjective_fg 𝒜 ℱ hcoh

  obtain ⟨d, k, f, hf⟩ := fg_graded_surjection_from_shifted_free 𝒜 M hfg

  obtain ⟨ψ, hψ⟩ := tildeProjFunctor_epi_of_surjection 𝒜 _ M f hf

  exact ⟨d, k, ψ ≫ iso.hom, epi_comp ψ iso.hom⟩

/-- Corollary 18: every coherent sheaf on `Proj 𝒜` is a quotient of a coproduct of
twisting sheaves `𝒪(-d)`, i.e. a quotient of a vector bundle. -/
theorem cor18_coherent_quotient_of_twisting
    (ℱ : (Proj 𝒜).Modules)
    (hcoh : CoherentSheafPred ℱ) :
    ∃ (d : ℕ) (k : ℕ),
      ∃ (φ : (∐ fun (_ : Fin k) => twistingSheaf 𝒜 (-(d : ℤ))) ⟶ ℱ),
        Epi φ := by

  obtain ⟨d, k, ψ, hψ⟩ := cor18_coherent_quotient_module_level 𝒜 ℱ hcoh

  exact ⟨d, k,
    (tilde_shifted_copies_iso_coproduct_twisting 𝒜 d k).inv ≫ ψ,
    epi_comp _ ψ⟩

/-- Proposition 21: `M̃ = 0` on `Proj 𝒜` iff `M` is locally nilpotent with respect to
the irrelevant ideal. -/
theorem prop21_tilde_zero_iff_locNilpotent
    (M : ZGradedModule 𝒜) :
    IsZero (tildeProjFunctor 𝒜 M) ↔ M.IsLocNilpotent := by sorry

/-- Proposition 21 for finitely generated modules: `M̃ = 0` iff `M` has finite total
dimension as a graded module. -/
theorem prop21_tilde_zero_iff_finDim
    (M : ZGradedModule 𝒜) (hfg : M.IsFG) :
    IsZero (tildeProjFunctor 𝒜 M) ↔ M.IsFinDim := by sorry

/-- Proposition 21 (Serre correspondence): `QCoh(Proj 𝒜)` is equivalent to the
category of graded `𝒜`-modules modulo locally nilpotent modules. -/
theorem prop21_serre_correspondence :

    (∀ (ℱ : (Proj 𝒜).Modules), IsQCoh ℱ →
      ∃ (M : ZGradedModule 𝒜), Nonempty (tildeProjFunctor 𝒜 M ≅ ℱ)) ∧

    (∀ (M : ZGradedModule 𝒜),
      IsZero (tildeProjFunctor 𝒜 M) ↔ M.IsLocNilpotent) ∧

    (∀ (M : ZGradedModule 𝒜), M.IsFG →
      (IsZero (tildeProjFunctor 𝒜 M) ↔ M.IsFinDim)) := by
  exact ⟨fun ℱ hqc => prop20_tildeFunctor_essentiallySurjective 𝒜 ℱ hqc,
         prop21_tilde_zero_iff_locNilpotent 𝒜,
         prop21_tilde_zero_iff_finDim 𝒜⟩

end ProjectiveQCohProperties

end
