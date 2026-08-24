/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Lemma22_10

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

section Theorem22_11
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

/-- Adèle-theoretic *index of speciality* of a divisor $D$: the difference
$g - 1 - r(D)$ between the genus and the Riemann defect at $D$. -/
noncomputable def adeleIndexOfSpeciality (D : P →₀ ℤ) : ℤ :=
  (genusVal_ax (F := F) (O := O) k : ℤ) - 1 -
    riemannDefect (F := F) (O := O) k D

/-- There exists a divisor $D_0$ whose Riemann defect attains the maximum
value $g - 1$, where $g$ is the genus of the function field. -/
theorem exists_defect_eq_genus_ax'
    {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O] :
    ∃ (D₀ : P →₀ ℤ),
      riemannDefect (F := F) (O := O) k D₀ =
        (genusVal_ax (F := F) (O := O) k : ℤ) - 1 :=
  genus_attained_ax k

/-- Given any divisor $D$, one can find a larger divisor $D' \geq D$ whose
Riemann defect attains the maximum value $g - 1$. -/
lemma exists_maximal_defect (D : P →₀ ℤ) :
    ∃ (D' : P →₀ ℤ), (∀ p, D p ≤ D' p) ∧
      riemannDefect (F := F) (O := O) k D' =
        (genusVal_ax (F := F) (O := O) k : ℤ) - 1 := by
  obtain ⟨D₀, hD₀⟩ := exists_defect_eq_genus_ax' (F := F) (O := O) k
  refine ⟨D ⊔ D₀, le_sup_left (a := D) (b := D₀), ?_⟩
  apply le_antisymm
  · exact riemannDefect_le_of_genus (F := F) (O := O) k (D ⊔ D₀)
  · rw [← hD₀]
    exact riemannDefect_mono k
      D₀ (D ⊔ D₀) (le_sup_right (a := D) (b := D₀))

/-- When $T = \top$ and $S \leq T$, the quotient $T / (T \cap S)$ is canonically
linearly equivalent to $M / S$. -/
noncomputable def quotientTopEquiv {R : Type*} [DivisionRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (S T : Submodule R M) (hT : T = ⊤) (hST : S ≤ T) :
    (↥T ⧸ Submodule.comap T.subtype S) ≃ₗ[R] (M ⧸ S) := by
  subst hT
  exact (Submodule.Quotient.equiv _ S Submodule.topEquiv (by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨y, _⟩, hym, rfl⟩; exact hym
    · intro hx; exact ⟨⟨x, trivial⟩, hx, rfl⟩))

/-- **Theorem 22.11.** The index of speciality $i(D)$ equals the $k$-dimension
of the adèle quotient $A_F / (A_F(D) + F)$; in particular this quotient is
finite-dimensional. -/
theorem speciality_eq_adele_quotient_dim (D : P →₀ ℤ) :
    FiniteDimensional k
      (FunctionFieldAdeleRing F P O ⧸
        AF_subspace (F := F) (O := O) k (D : P → ℤ)) ∧
    (Module.finrank k
      (FunctionFieldAdeleRing F P O ⧸
        AF_subspace (F := F) (O := O) k (D : P → ℤ)) : ℤ) =
      adeleIndexOfSpeciality (F := F) (O := O) k D := by

  obtain ⟨D', hD'_ge, hrD'⟩ := exists_maximal_defect (F := F) (O := O) k D

  have hAF_top : AF_subspace (F := F) (O := O) k (D' : P → ℤ) = ⊤ :=
    AF_subspace_eq_top k D' hrD'

  have h_dim := AF_subspace_dim (F := F) (O := O) k D D' hD'_ge
  obtain ⟨hFD, h_dim_eq⟩ := h_dim
  haveI := hFD

  set S := AF_subspace (F := F) (O := O) k (D : P → ℤ) with hS_def
  set T := AF_subspace (F := F) (O := O) k (D' : P → ℤ) with hT_def
  have h_le : S ≤ T := AF_subspace_mono k hD'_ge

  let qe := quotientTopEquiv S T hAF_top h_le
  constructor
  ·
    exact Module.Finite.equiv qe
  ·
    have h_rank : Module.finrank k (FunctionFieldAdeleRing F P O ⧸ S) =
        Module.finrank k (↥T ⧸ Submodule.comap T.subtype S) :=
      (LinearEquiv.finrank_eq qe).symm
    push_cast [h_rank]
    rw [h_dim_eq, hrD']
    unfold adeleIndexOfSpeciality
    ring

end Theorem22_11
