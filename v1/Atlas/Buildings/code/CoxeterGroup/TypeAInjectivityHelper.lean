/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.SetTheory.Cardinal.Finite

open Equiv Fin Function

/-- Braid relation: $(\operatorname{swap}(a,b) \cdot \operatorname{swap}(b,c))^3 = 1$ for distinct $a,b,c$. -/
lemma swap_mul_swap_cube {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (swap a b * swap b c) ^ 3 = 1 := by
  have h1 := swap_mul_swap_mul_swap hab hac
  have h2 : swap a b * swap c a * swap a b = swap b c := by
    have := swap_mul_swap_mul_swap hac.symm (Ne.symm hbc)
    simp only [swap_comm] at this ⊢; exact this
  show swap a b * swap b c * (swap a b * swap b c) * (swap a b * swap b c) = 1
  calc swap a b * swap b c * (swap a b * swap b c) * (swap a b * swap b c)
      = swap a b * (swap b c * swap a b * swap b c) * (swap a b * swap b c) := by
        simp only [mul_assoc]
    _ = swap a b * swap c a * swap a b * swap b c := by rw [h1]; simp only [mul_assoc]
    _ = swap b c * swap b c := by rw [h2]
    _ = 1 := swap_mul_self b c

/-- Reversed braid relation: $(\operatorname{swap}(b,c) \cdot \operatorname{swap}(a,b))^3 = 1$. -/
lemma swap_mul_swap_cube' {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (swap b c * swap a b) ^ 3 = 1 := by
  rw [show swap b c * swap a b = (swap a b * swap b c)⁻¹ from by
    rw [mul_inv_rev, swap_inv, swap_inv]]
  rw [inv_pow, swap_mul_swap_cube hab hbc hac, inv_one]

set_option maxHeartbeats 400000 in
/-- The assignment $i \mapsto \operatorname{swap}(\operatorname{castSucc} i, \operatorname{succ} i)$
satisfies the type-$A$ Coxeter relations. -/
theorem adjTransp_isLiftable (n : ℕ) :
    (CoxeterMatrix.A n).IsLiftable (fun i : Fin n => swap (castSucc i) (succ i)) := by
  intro i j
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs with hij hadj
  ·
    subst hij; simp [swap_mul_self]
  ·
    rcases hadj with h1 | h2
    ·
      conv_lhs =>
        rw [show (castSucc i : Fin (n + 1)) = succ j from by
          ext; simp [Fin.val_succ, Fin.val_castSucc]; omega]
      apply swap_mul_swap_cube'
      · intro h; simp [Fin.ext_iff] at h
      · intro h; exact hij (Fin.ext (by simpa using congr_arg Fin.val h)).symm
      · intro h
        have := congr_arg Fin.val h; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
    ·
      conv_lhs =>
        rw [show (castSucc j : Fin (n + 1)) = succ i from by
          ext; simp [Fin.val_succ, Fin.val_castSucc]; omega]
      apply swap_mul_swap_cube
      · intro h; simp [Fin.ext_iff] at h
      · intro h; exact hij (Fin.ext (by simpa using congr_arg Fin.val h))
      · intro h
        have := congr_arg Fin.val h; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
  ·
    have hne : i ≠ j := hij
    push Not at hadj
    obtain ⟨hnadj1, hnadj2⟩ := hadj
    have hci_cj : (castSucc i : Fin (n + 1)) ≠ castSucc j := by
      intro h; exact hne (Fin.ext (by simpa [Fin.val_castSucc] using congr_arg Fin.val h))
    have hsi_sj : (succ i : Fin (n + 1)) ≠ succ j := by
      intro h; exact hne (Fin.ext (by simpa [Fin.val_succ] using congr_arg Fin.val h))
    have hci_sj : (castSucc i : Fin (n + 1)) ≠ succ j := by
      intro h
      have := congr_arg Fin.val h; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
    have hsi_cj : (succ i : Fin (n + 1)) ≠ castSucc j := by
      intro h
      have := congr_arg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
    have hdisjoint : (swap (castSucc i) (succ i) : Equiv.Perm (Fin (n + 1))).Disjoint
        (swap (castSucc j) (succ j)) := by
      intro x
      by_cases hxcj : x = castSucc j
      · left; subst hxcj; exact swap_apply_of_ne_of_ne hci_cj.symm hsi_cj.symm
      · by_cases hxsj : x = succ j
        · left; subst hxsj; exact swap_apply_of_ne_of_ne hci_sj.symm hsi_sj.symm
        · right; exact swap_apply_of_ne_of_ne hxcj hxsj
    rw [Commute.mul_pow hdisjoint.commute, sq, sq, swap_mul_self, swap_mul_self, mul_one]

/-- The type-$A$ Coxeter relations evaluate to $1$ under the assignment to adjacent transpositions. -/
theorem typeA_relations_satisfied (n : ℕ) :
    ∀ r ∈ (CoxeterMatrix.A n).relationsSet,
      (FreeGroup.lift (fun (i : Fin n) => swap (castSucc i) (succ i))) r = 1 := by
  intro r ⟨⟨i, j⟩, hrij⟩
  rw [← hrij]
  simp only [uncurry, CoxeterMatrix.relation, map_pow, map_mul, FreeGroup.lift_apply_of]
  exact adjTransp_isLiftable n i j

/-- Upper bound on the cardinality of the type-$A_{n-1}$ Coxeter group: $|W(A_{n-1})| \le (n+1)!$. -/
theorem typeA_coxeterGroup_mk_le (n : ℕ) :
    Cardinal.mk (CoxeterMatrix.A n).Group ≤ ↑(n + 1).factorial := by sorry

/-- The type-$A_{n-1}$ Coxeter group is finite. -/
theorem typeA_coxeterGroup_finite (n : ℕ) : Finite (CoxeterMatrix.A n).Group := by
  have h1 : Cardinal.mk (CoxeterMatrix.A n).Group < Cardinal.aleph0 :=
    lt_of_le_of_lt (typeA_coxeterGroup_mk_le n) Cardinal.natCast_lt_aleph0
  rwa [Cardinal.lt_aleph0_iff_finite] at h1

/-- $|W(A_{n-1})| \le (n+1)!$ as a natural number bound. -/
theorem typeA_coxeterGroup_card_le (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group ≤ (n + 1).factorial := by
  haveI := typeA_coxeterGroup_finite n
  rw [Nat.card]
  have := Cardinal.toNat_le_toNat (typeA_coxeterGroup_mk_le n) Cardinal.natCast_lt_aleph0
  rwa [Cardinal.toNat_natCast] at this

/-- The presented-group hom $W(A_{n-1}) \to S_{n+1}$ via adjacent transpositions is surjective. -/
theorem typeA_toPermHom_surjective (n : ℕ)
    (h : ∀ r ∈ (CoxeterMatrix.A n).relationsSet,
      (FreeGroup.lift (fun (i : Fin n) => swap (castSucc i) (succ i))) r = 1) :
    Function.Surjective
      (PresentedGroup.toGroup h : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1))) := by
  set φ := (PresentedGroup.toGroup h : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)))
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  have hgen : ∀ i : Fin n, swap (castSucc i) (succ i) ∈ φ.range := fun i =>
    MonoidHom.mem_range.mpr ⟨PresentedGroup.of i, PresentedGroup.toGroup.of h⟩
  intro σ _
  have hmcl := Equiv.Perm.mclosure_swap_castSucc_succ n
  have hσ : σ ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap (Fin.castSucc i) (Fin.succ i)) := by
    rw [hmcl]; exact Submonoid.mem_top σ
  apply (Submonoid.closure_le.mpr _) hσ
  intro x hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  exact hgen i

/-- Exact cardinality: $|W(A_{n-1})| = (n+1)!$, matching $|S_{n+1}|$. -/
theorem typeA_coxeterGroup_card_eq_factorial (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group = (n + 1).factorial := by
  haveI : Finite (CoxeterMatrix.A n).Group := typeA_coxeterGroup_finite n
  haveI : Finite (PresentedGroup (CoxeterMatrix.A n).relationsSet) :=
    ‹Finite (CoxeterMatrix.A n).Group›

  have h_le := typeA_coxeterGroup_card_le n

  have h := typeA_relations_satisfied n
  have hsurj := typeA_toPermHom_surjective n h
  have h_ge : (n + 1).factorial ≤ Nat.card (CoxeterMatrix.A n).Group := by
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
  exact le_antisymm h_le h_ge

/-- Injectivity of the presented-group hom $W(A_{n-1}) \to S_{n+1}$, deduced from matching cardinalities. -/
theorem typeA_coxeterGroup_toPermHom_injective (n : ℕ)
    (h : ∀ r ∈ (CoxeterMatrix.A n).relationsSet,
      (FreeGroup.lift (fun (i : Fin n) => swap (castSucc i) (succ i))) r = 1) :
    Function.Injective
      (PresentedGroup.toGroup h : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1))) := by

  haveI : Finite (CoxeterMatrix.A n).Group := typeA_coxeterGroup_finite n
  haveI : Finite (PresentedGroup (CoxeterMatrix.A n).relationsSet) :=
    ‹Finite (CoxeterMatrix.A n).Group›
  set φ := (PresentedGroup.toGroup h : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)))

  have hcard : Nat.card (CoxeterMatrix.A n).Group = Nat.card (Equiv.Perm (Fin (n + 1))) := by
    rw [typeA_coxeterGroup_card_eq_factorial, Nat.card_eq_fintype_card,
        Fintype.card_perm, Fintype.card_fin]

  have hsurj : Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro σ _
    have hgen : ∀ i : Fin n, swap (castSucc i) (succ i) ∈ φ.range := by
      intro i; exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of h⟩
    have hσ : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap (Fin.castSucc i) (Fin.succ i)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top σ
    apply Submonoid.closure_le.mpr _ hσ
    intro x hx; obtain ⟨i, hi⟩ := hx; rw [← hi]; exact hgen i

  exact ((Nat.bijective_iff_surjective_and_card φ).mpr ⟨hsurj, hcard⟩).1

/-- Group isomorphism $W(A_{n-1}) \cong S_{n+1}$. -/
noncomputable def typeA_mulEquiv (n : ℕ) :
    (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)) :=
  MulEquiv.ofBijective
    (PresentedGroup.toGroup (typeA_relations_satisfied n))
    ⟨typeA_coxeterGroup_toPermHom_injective n (typeA_relations_satisfied n),
     typeA_toPermHom_surjective n (typeA_relations_satisfied n)⟩

/-- Reverse isomorphism $S_{n+1} \cong W(A_{n-1})$. -/
noncomputable def typeA_symGroup_mulEquiv (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) ≃* (CoxeterMatrix.A n).Group := by sorry

/-- Under the symmetric-group/Coxeter-group isomorphism, the $i$-th Coxeter generator corresponds
to the adjacent transposition swapping $i$ and $i+1$. -/
theorem typeA_symGroup_mulEquiv_apply (n : ℕ) (i : Fin n) :
    (typeA_symGroup_mulEquiv n).symm (PresentedGroup.of i) =
    Equiv.swap (Fin.castSucc i) (Fin.succ i) := by sorry

/-- Short alias for the cardinality formula $|W(A_{n-1})| = (n+1)!$. -/
theorem typeA_card_eq (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group = (n + 1).factorial :=
  typeA_coxeterGroup_card_eq_factorial n
