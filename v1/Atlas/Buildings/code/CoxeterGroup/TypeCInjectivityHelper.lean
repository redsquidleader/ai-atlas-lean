/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.SetTheory.Cardinal.Finite
import Atlas.Buildings.code.CoxeterGroup.SignedPermGroup

open Equiv Fin Function SignedPerm

/-- The $i$-th Coxeter generator of type $C_n$: an adjacent transposition for $i < n-1$, or the
sign change at the last coordinate when $i = n-1$. -/
noncomputable def typeCGen {n : ℕ} (i : Fin n) : SignedPermGroup n :=
  if h : (i : ℕ) + 1 < n then
    SemidirectProduct.inr (Equiv.swap (i : Fin n) ⟨i + 1, h⟩)
  else
    SemidirectProduct.inl (signChangeAt n ⟨n - 1, by omega⟩)

/-- The type-$C_n$ Coxeter group is finite. -/
theorem typeC_coxeterGroup_finite (n : ℕ) : Finite (CoxeterMatrix.B n).Group := by sorry

/-- Upper bound on the type-$C_n$ Coxeter group: $|W(C_n)| \le 2^n \cdot n!$. -/
theorem typeC_coxeterGroup_card_le (n : ℕ) :
    Nat.card (CoxeterMatrix.B n).Group ≤ 2 ^ n * n.factorial := by sorry

/-- The chosen signed permutations $\{\text{typeCGen}\ i\}$ satisfy all type-$C_n$ Coxeter relations. -/
theorem typeC_generators_isLiftable (n : ℕ) :
    (CoxeterMatrix.B n).IsLiftable (fun i : Fin n => typeCGen i) := by sorry

/-- Every type-$C_n$ Coxeter relation evaluates to $1$ under the assignment to `typeCGen`. -/
theorem typeC_relations_satisfied (n : ℕ) :
    ∀ r ∈ (CoxeterMatrix.B n).relationsSet,
      (FreeGroup.lift (fun i : Fin n => typeCGen i)) r = 1 := by
  intro r ⟨⟨i, j⟩, hrij⟩
  rw [← hrij]
  simp only [uncurry, CoxeterMatrix.relation, map_pow, map_mul, FreeGroup.lift_apply_of]
  exact typeC_generators_isLiftable n i j

/-- Canonical homomorphism $W(C_n) \to S_n^\pm$ sending each Coxeter generator to the corresponding
`typeCGen`. -/
noncomputable def typeCHom (n : ℕ) :
    (CoxeterMatrix.B n).Group →* SignedPermGroup n :=
  PresentedGroup.toGroup (typeC_relations_satisfied n)

/-- The presented-group hom sends the $i$-th simple generator to `typeCGen i`. -/
theorem typeCHom_of (n : ℕ) (i : Fin n) :
    typeCHom n (PresentedGroup.of i) = typeCGen i :=
  PresentedGroup.toGroup.of (typeC_relations_satisfied n)

/-- Every permutation $\sigma \in S_n$, viewed inside $S_n^\pm$ via $\inr$, lies in the range of `typeCHom`. -/
theorem typeCHom_inr_mem_range : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    (SemidirectProduct.inr σ : SignedPermGroup n) ∈ (typeCHom n).range
  | 0, σ => ⟨1, by
      rw [map_one]
      apply SemidirectProduct.ext
      · funext i; exact Fin.elim0 i
      · ext i; exact Fin.elim0 i⟩
  | m + 1, σ => by


    apply inr_mem_of_adj_swaps_mem m σ (typeCHom (m + 1)).range
    intro i


    refine ⟨PresentedGroup.of ⟨i.val, by omega⟩, ?_⟩
    rw [typeCHom_of]
    simp only [typeCGen]
    have hi : (⟨i.val, by omega⟩ : Fin (m + 1)).val + 1 < m + 1 := by simp
    rw [dif_pos hi]
    congr 1

/-- Every sign vector $\varepsilon \in (\{\pm 1\})^n$, viewed via $\inl$, lies in the range of `typeCHom`. -/
theorem typeCHom_inl_mem_range (n : ℕ) (ε : SignGroup n) :
    (SemidirectProduct.inl ε : SignedPermGroup n) ∈ (typeCHom n).range := by


  apply inl_mem_of_signChangeAt_mem
  intro j


  by_cases hn : n = 0
  · exact (Fin.elim0 (hn ▸ j))
  ·
    have hn' : 0 < n := Nat.pos_of_ne_zero hn

    have hlast_gen : typeCHom n (PresentedGroup.of ⟨n - 1, by omega⟩) =
        SemidirectProduct.inl (signChangeAt n ⟨n - 1, by omega⟩) := by
      rw [typeCHom_of]
      simp only [typeCGen]
      have : ¬((⟨n - 1, by omega⟩ : Fin n).val + 1 < n) := by simp; omega
      rw [dif_neg this]

    rw [show signChangeAt n j =
      (signGroupPermAction n (Equiv.swap j ⟨n - 1, by omega⟩))
        (signChangeAt n ⟨n - 1, by omega⟩) from by
      rw [signGroupPermAction_signChangeAt]; simp]

    rw [← inr_conj_inl]
    apply Subgroup.mul_mem
    apply Subgroup.mul_mem
    · exact typeCHom_inr_mem_range n (Equiv.swap j ⟨n - 1, by omega⟩)
    · exact ⟨PresentedGroup.of ⟨n - 1, by omega⟩, hlast_gen⟩
    · exact Subgroup.inv_mem _ (typeCHom_inr_mem_range n (Equiv.swap j ⟨n - 1, by omega⟩))

/-- `typeCHom n` is surjective onto $S_n^\pm$. -/
theorem typeCHom_surjective (n : ℕ) : Function.Surjective (typeCHom n) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro g _

  have hg : g = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right := by
    cases g with | mk l r => simp [SemidirectProduct.mk_eq_inl_mul_inr]
  rw [hg]
  apply Subgroup.mul_mem
  ·
    apply typeCHom_inl_mem_range
  ·
    apply typeCHom_inr_mem_range

/-- Exact cardinality: $|W(C_n)| = 2^n \cdot n!$, matching $|S_n^\pm|$. -/
theorem typeC_coxeterGroup_card_eq (n : ℕ) :
    Nat.card (CoxeterMatrix.B n).Group = 2 ^ n * n.factorial := by
  haveI : Finite (CoxeterMatrix.B n).Group := typeC_coxeterGroup_finite n
  haveI : Finite (PresentedGroup (CoxeterMatrix.B n).relationsSet) :=
    ‹Finite (CoxeterMatrix.B n).Group›
  have h_le := typeC_coxeterGroup_card_le n
  have h_ge : 2 ^ n * n.factorial ≤ Nat.card (CoxeterMatrix.B n).Group := by
    have := Nat.card_le_card_of_surjective _ (typeCHom_surjective n)
    rwa [signedPermGroup_card] at this
  exact le_antisymm h_le h_ge

/-- `typeCHom n` is injective: it is therefore a group isomorphism $W(C_n) \cong S_n^\pm$. -/
theorem typeCHom_injective (n : ℕ) : Function.Injective (typeCHom n) := by
  haveI : Finite (CoxeterMatrix.B n).Group := typeC_coxeterGroup_finite n
  haveI : Finite (PresentedGroup (CoxeterMatrix.B n).relationsSet) :=
    ‹Finite (CoxeterMatrix.B n).Group›
  have hcard : Nat.card (CoxeterMatrix.B n).Group = Nat.card (SignedPermGroup n) := by
    rw [typeC_coxeterGroup_card_eq, signedPermGroup_card]
  exact ((Nat.bijective_iff_surjective_and_card (typeCHom n)).mpr
    ⟨typeCHom_surjective n, hcard⟩).1

/-- Group isomorphism $W(C_n) \cong S_n^\pm$, packaging `typeCHom` as a `MulEquiv`. -/
noncomputable def typeC_mulEquiv_forward (n : ℕ) :
    (CoxeterMatrix.B n).Group ≃* SignedPermGroup n :=
  MulEquiv.ofBijective (typeCHom n) ⟨typeCHom_injective n, typeCHom_surjective n⟩

/-- Reverse isomorphism $S_n^\pm \cong W(C_n)$. -/
noncomputable def typeC_signedPerm_mulEquiv (n : ℕ) :
    SignedPermGroup n ≃* (CoxeterMatrix.B n).Group :=
  (typeC_mulEquiv_forward n).symm
