/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SerreDualityTate

noncomputable section

namespace SerreDualityAnnihilator

open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology


section AnnihilatorEqualities

variable {k : Type*} [Field k]

/-- If `f : ℤ →₀ k` is supported in nonnegative degrees, then it lies in the annihilator
of any `g` supported in nonnegative degrees under the residue pairing `(f, g) ↦ ∑ j f j · g (-1 - j)`. -/
theorem annihilator_nonneg_reverse (f : ℤ →₀ k) :
    (∀ (i : ℤ), i < 0 → f i = 0) →
    (∀ g : ℤ →₀ k, (∀ (i : ℤ), i < 0 → g i = 0) →
      (∑ j ∈ f.support, f j * g (-1 - j)) = 0) := by
  intro hf g hg
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj0 : j < 0
  · simp [hf j hj0]
  · push Not at hj0
    have h_neg : -1 - j < 0 := by omega
    simp [hg (-1 - j) h_neg]

/-- Annihilator characterization: `f` annihilates every nonneg-supported `g`
under the residue pairing if and only if `f` is itself nonneg-supported. -/
theorem annihilator_nonneg_iff (f : ℤ →₀ k) :
    (∀ g : ℤ →₀ k, (∀ (i : ℤ), i < 0 → g i = 0) →
      (∑ j ∈ f.support, f j * g (-1 - j)) = 0) ↔
    (∀ (i : ℤ), i < 0 → f i = 0) :=
  ⟨SerreDualityTate.lattice_annihilator_nonneg f,
   annihilator_nonneg_reverse f⟩

/-- An `f` supported in strictly negative degrees annihilates every `g`
supported in strictly negative degrees under the residue pairing. -/
theorem strictly_neg_annihilates_strictly_neg (f : ℤ →₀ k)
    (hf : ∀ (i : ℤ), 0 ≤ i → f i = 0) :
    ∀ g : ℤ →₀ k, (∀ (i : ℤ), 0 ≤ i → g i = 0) →
      (∑ j ∈ g.support, g j * f (-1 - j)) = 0 := by
  intro g hg
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj0 : 0 ≤ j
  · simp [hg j hj0]
  · push Not at hj0
    have h_nonneg : 0 ≤ -1 - j := by omega
    simp [hf (-1 - j) h_nonneg]

/-- Converse: if `f` annihilates every strictly-negative-supported `g`
under the residue pairing, then `f` is supported in strictly negative degrees. -/
theorem annihilator_strictly_neg (f : ℤ →₀ k) :
    (∀ g : ℤ →₀ k, (∀ (i : ℤ), 0 ≤ i → g i = 0) →
      (∑ j ∈ g.support, g j * f (-1 - j)) = 0) →
    ∀ (i : ℤ), 0 ≤ i → f i = 0 := by
  intro hpair i hi
  specialize hpair (Finsupp.single (-1 - i) 1) (fun j hj => by
    simp only [Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · rfl)
  have hsupp : (Finsupp.single (-1 - i) (1 : k)).support = {-1 - i} := by
    rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  rw [hsupp, Finset.sum_singleton] at hpair
  simp only [Finsupp.single_apply, ↓reduceIte, one_mul,
    show (-1 : ℤ) - (-1 - i) = i from by omega] at hpair
  exact hpair

/-- Biconditional version: the annihilator of the nonneg-supported subspace
under the residue pairing is exactly the strictly-negative-supported subspace. -/
theorem annihilator_strictly_neg_iff (f : ℤ →₀ k) :
    (∀ g : ℤ →₀ k, (∀ (i : ℤ), 0 ≤ i → g i = 0) →
      (∑ j ∈ g.support, g j * f (-1 - j)) = 0) ↔
    (∀ (i : ℤ), 0 ≤ i → f i = 0) :=
  ⟨annihilator_strictly_neg f,
   strictly_neg_annihilates_strictly_neg f⟩

end AnnihilatorEqualities


section TateDualitySelfDual

variable {k : Type*} [Field k]

open Module FiniteDimensional Submodule

/-- Tate-style duality: for a self-dual pairing `B : V ≃ V*`, the dimension of
`B⁻¹(W₁⁰) ∩ B⁻¹(W₂⁰)` equals the codimension of `W₁ + W₂` in `V`. -/
theorem tate_duality_via_pairing {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (B : V ≃ₗ[k] Module.Dual k V)
    (W₁ W₂ : Submodule k V) :
    finrank k ↥(W₁.dualAnnihilator.comap B.toLinearMap ⊓
                 W₂.dualAnnihilator.comap B.toLinearMap) =
    finrank k (V ⧸ (W₁ ⊔ W₂)) := by
  rw [← Submodule.comap_inf, ← Submodule.dualAnnihilator_sup_eq]
  have h_eq : Submodule.map B.toLinearMap
      ((W₁ ⊔ W₂).dualAnnihilator.comap B.toLinearMap) =
      (W₁ ⊔ W₂).dualAnnihilator :=
    Submodule.map_comap_eq_of_surjective B.surjective _
  have h_finrank : finrank k ↥((W₁ ⊔ W₂).dualAnnihilator.comap B.toLinearMap) =
      finrank k ↥(W₁ ⊔ W₂).dualAnnihilator :=
    LinearEquiv.finrank_eq ((B.submoduleMap _).trans (LinearEquiv.ofEq _ _ h_eq))
  rw [h_finrank]
  have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (W₁ ⊔ W₂)
  have h_quot := Submodule.finrank_quotient_add_finrank (W₁ ⊔ W₂)
  omega

/-- Restated form of `tate_duality_via_pairing` where the annihilator subspaces
`W₁'` and `W₂'` are given as hypotheses. -/
theorem tate_duality_via_self_duality {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (B : V ≃ₗ[k] Module.Dual k V)
    (W₁ W₂ W₁' W₂' : Submodule k V)
    (h₁ : W₁' = W₁.dualAnnihilator.comap B.toLinearMap)
    (h₂ : W₂' = W₂.dualAnnihilator.comap B.toLinearMap) :
    finrank k ↥(W₁' ⊓ W₂') = finrank k (V ⧸ (W₁ ⊔ W₂)) := by
  subst h₁; subst h₂
  exact tate_duality_via_pairing B W₁ W₂

/-- Euler-characteristic identity: for any two subspaces of a finite-dimensional `V`,
`dim(W₁ ∩ W₂) - dim(V/(W₁ + W₂)) = dim W₁ + dim W₂ - dim V`. -/
theorem tate_euler_char_self_dual {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (W₁ W₂ : Submodule k V) :
    (finrank k ↥(W₁ ⊓ W₂) : ℤ) - finrank k (V ⧸ (W₁ ⊔ W₂)) =
    finrank k W₁ + finrank k W₂ - finrank k V := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  have hq := Submodule.finrank_quotient_add_finrank (W₁ ⊔ W₂)
  omega

/-- Symmetric form combining Tate duality and the Euler identity, relating
`dim(W₁ ∩ W₂) + dim(W₁' ∩ W₂')` to the dimensions of `W₁`, `W₂`, `V`,
and the codimension of `W₁ + W₂`. -/
theorem tate_duality_symmetric {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (B : V ≃ₗ[k] Module.Dual k V)
    (W₁ W₂ W₁' W₂' : Submodule k V)
    (h₁ : W₁' = W₁.dualAnnihilator.comap B.toLinearMap)
    (h₂ : W₂' = W₂.dualAnnihilator.comap B.toLinearMap) :
    (finrank k ↥(W₁ ⊓ W₂) : ℤ) + finrank k ↥(W₁' ⊓ W₂') =
    finrank k W₁ + finrank k W₂ - finrank k V +
    2 * finrank k (V ⧸ (W₁ ⊔ W₂)) := by
  have htate := tate_duality_via_self_duality B W₁ W₂ W₁' W₂' h₁ h₂
  have heuler := tate_euler_char_self_dual W₁ W₂
  omega

end TateDualitySelfDual


section P1Connection

variable (k : Type) [Field k]

/-- For `n < -1`, the Čech `H¹(O(n))` on `ℙ¹` realizes Tate-style duality:
its dimension equals `dim H⁰(O(-2 - n))`. -/
theorem shift_realizes_tate_duality (n : ℤ) (hn : n < -1) :
    Module.finrank k ((ℤ →₀ k) ⧸ (CohomologyP1.NonNeg k ⊔ CohomologyP1.AtMost k n)) =
    Module.finrank k ↥(CechH0 k (-2 - n)) :=
  SerreDualityP1.serre_duality_finrank k n hn

/-- Both directions of Serre duality on `ℙ¹`: `dim H¹(O(n)) = dim H⁰(O(-2-n))`
and `dim H⁰(O(n)) = dim H¹(O(-2-n))`. -/
theorem serre_duality_P1_both_directions (n : ℤ) :
    RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) ∧
    RiemannRoch.dimH0 k n = RiemannRoch.dimH1 k (-2 - n) := by
  constructor
  · exact RiemannRoch.serre_duality_P1 k n
  · have h := RiemannRoch.serre_duality_P1 k (-2 - n)
    have heq : -2 - (-2 - n) = n := by omega
    rw [heq] at h
    exact h.symm

/-- Bundles Serre duality on `ℙ¹` (both directions) together with the
Riemann–Roch formula `χ(O(n)) = n + 1`. -/
theorem serre_duality_chain_P1 (n : ℤ) :

    RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) ∧

    RiemannRoch.dimH0 k n = RiemannRoch.dimH1 k (-2 - n) ∧

    (RiemannRoch.dimH0 k n : ℤ) - (RiemannRoch.dimH1 k n : ℤ) = n + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (serre_duality_P1_both_directions k n).1
  · exact (serre_duality_P1_both_directions k n).2
  · exact RiemannRoch.riemann_roch_P1 k n

end P1Connection


section GeneralCurves

/-- For a smooth complete curve `C` and degree `d`, the sum
`χ(O(d)) + χ(O(K - d)) = 0`, the Euler-characteristic shadow of Serre duality. -/
theorem serre_duality_general_strategy (C : SmoothCompleteCurve) (d : ℤ) :
    C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
  SerreDualityCurves.serre_duality_chi_rank1 C d

end GeneralCurves


section AbstractExplainsP1

variable (k : Type) [Field k]

/-- The abstract Serre duality matches the explicit `ℙ¹` computation:
`dim H⁰(O(-2-n)) = dim H¹(O(n))`. -/
theorem abstract_matches_P1 (n : ℤ) :


    RiemannRoch.dimH0 k (-2 - n) = RiemannRoch.dimH1 k n :=
  (RiemannRoch.serre_duality_P1 k n).symm

/-- The Tate-vector-space duality applied to the `ℙ¹` Čech setup yields the
equality of `H¹(O(n))` and `H⁰(O(-2 - n))` dimensions, for `n < -1`. -/
theorem tate_applied_to_P1 (n : ℤ) (hn : n < -1) :
    Module.finrank k (SerreDualityTate.cechSetup_P1 k n).cechH1 =
    Module.finrank k ↥(CechH0 k (-2 - n)) :=
  SerreDualityP1.serre_duality_finrank k n hn

end AbstractExplainsP1

end SerreDualityAnnihilator

end
