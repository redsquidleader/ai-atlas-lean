/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace CoherentLineBundlesProj

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Predicate asserting that a sheaf of modules `ℱ` on a scheme `Y` is coherent. -/
noncomputable def IsCoherent {Y : Scheme.{u}} (ℱ : Y.Modules) : Prop := by sorry

/-- The Serre twisting sheaf `O(d)` on `Proj 𝒜` for an integer `d`. -/
noncomputable def twistingSheafProj (d : ℤ) : (Proj 𝒜).Modules := by sorry

/-- The type of finitely generated graded modules over the graded ring `𝒜`. -/
noncomputable def FGGradedModule
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : Type u := by sorry

/-- The sheaf `M̃` on `Proj 𝒜` associated to a finitely generated graded module `M`. -/
noncomputable def tildeSheaf (M : FGGradedModule 𝒜) : (Proj 𝒜).Modules := by sorry

/-- Every coherent sheaf on `Proj 𝒜` arises (up to isomorphism) as `M̃` for some finitely generated
graded module `M`. -/
theorem prop20_coherent_from_fg_module
    (ℱ : (Proj 𝒜).Modules) (hcoh : IsCoherent ℱ) :
    ∃ (M : FGGradedModule 𝒜), Nonempty (tildeSheaf 𝒜 M ≅ ℱ) := by sorry

/-- For any finitely generated graded module `M`, there exists a surjection from a finite direct
sum of twisting sheaves `O(-d)` onto `M̃`. -/
theorem fg_module_line_bundle_surjection
    (M : FGGradedModule 𝒜) :
    ∃ (d : ℕ) (r : ℕ),
      ∃ (φ : (∐ fun (_ : Fin r) => twistingSheafProj 𝒜 (-(d : ℤ))) ⟶ tildeSheaf 𝒜 M),
        Epi φ := by sorry

/-- Serre's theorem: every coherent sheaf on `Proj 𝒜` is a quotient of a finite direct sum of
Serre twisting sheaves `O(-d)`. -/
theorem serre_coherent_presentation
    (ℱ : (Proj 𝒜).Modules) (hcoh : IsCoherent ℱ) :
    ∃ (d : ℕ) (r : ℕ),
      ∃ (φ : (∐ fun (_ : Fin r) => twistingSheafProj 𝒜 (-(d : ℤ))) ⟶ ℱ),
        Epi φ := by

  obtain ⟨M, ⟨i⟩⟩ := prop20_coherent_from_fg_module 𝒜 ℱ hcoh

  obtain ⟨d, r, φ, hφ⟩ := fg_module_line_bundle_surjection 𝒜 M

  exact ⟨d, r, φ ≫ i.hom, epi_comp φ i.hom⟩

end CoherentLineBundlesProj

end
