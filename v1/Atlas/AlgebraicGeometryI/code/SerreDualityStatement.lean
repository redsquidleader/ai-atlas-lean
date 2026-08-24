/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

universe u

namespace SerreDualityStatement

/-- Abstract vector-space-level model of a smooth complete curve over `k`:
locally free sheaves with finite-dimensional global sections and `H¹`,
together with a Serre dual involution and distinguished `O_X`, `K_X`. -/
structure SmoothCompleteCurveVS (k : Type u) [Field k] where
  LocallyFreeSheaf : Type u
  globalSections : LocallyFreeSheaf → Type u
  globalSections_addCommGroup : ∀ E, AddCommGroup (globalSections E)
  globalSections_module : ∀ E, Module k (globalSections E)
  globalSections_finiteDimensional : ∀ E, Module.Finite k (globalSections E)
  H1 : LocallyFreeSheaf → Type u
  H1_addCommGroup : ∀ E, AddCommGroup (H1 E)
  H1_module : ∀ E, Module k (H1 E)
  H1_finiteDimensional : ∀ E, Module.Finite k (H1 E)
  serreDual : LocallyFreeSheaf → LocallyFreeSheaf
  canonicalSheaf : LocallyFreeSheaf
  structureSheaf : LocallyFreeSheaf
  serreDual_globalSections_equiv : ∀ E,
    globalSections (serreDual (serreDual E)) ≃ₗ[k] globalSections E
  serreDual_H1_equiv : ∀ E,
    H1 (serreDual (serreDual E)) ≃ₗ[k] H1 E

variable {k : Type u} [Field k]

attribute [instance] SmoothCompleteCurveVS.globalSections_addCommGroup
attribute [instance] SmoothCompleteCurveVS.globalSections_module
attribute [instance] SmoothCompleteCurveVS.globalSections_finiteDimensional
attribute [instance] SmoothCompleteCurveVS.H1_addCommGroup
attribute [instance] SmoothCompleteCurveVS.H1_module
attribute [instance] SmoothCompleteCurveVS.H1_finiteDimensional

/-- Serre duality (Thm 24.3): for a locally free sheaf `E` on a complete smooth
irreducible curve, the canonical isomorphism `Γ(E)* ≅ H¹(E∨ ⊗ K_X)`. -/
noncomputable def serre_duality_iso (X : SmoothCompleteCurveVS k) (E : X.LocallyFreeSheaf) :
    Module.Dual k (X.globalSections E) ≃ₗ[k] X.H1 (X.serreDual E) := by sorry

/-- Serre duality at the dimension level: `dim Γ(E) = dim H¹(E∨ ⊗ K_X)`. -/
theorem serre_duality_finrank_general (X : SmoothCompleteCurveVS k) (E : X.LocallyFreeSheaf) :
    Module.finrank k (X.globalSections E) = Module.finrank k (X.H1 (X.serreDual E)) := by
  rw [← Subspace.dual_finrank_eq (K := k) (V := X.globalSections E)]
  exact LinearEquiv.finrank_eq (serre_duality_iso X E)

/-- Reverse direction of Serre duality: `dim H¹(E) = dim Γ(E∨ ⊗ K_X)`, obtained
by applying the forward statement to `E∨ ⊗ K_X` and using the involution. -/
theorem serre_duality_reverse_finrank_general (X : SmoothCompleteCurveVS k)
    (E : X.LocallyFreeSheaf) :
    Module.finrank k (X.H1 E) = Module.finrank k (X.globalSections (X.serreDual E)) := by
  have hfwd := serre_duality_finrank_general X (X.serreDual E)
  have hH1 : Module.finrank k (X.H1 (X.serreDual (X.serreDual E))) =
      Module.finrank k (X.H1 E) :=
    LinearEquiv.finrank_eq (X.serreDual_H1_equiv E)
  linarith

end SerreDualityStatement
