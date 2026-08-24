/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch

namespace RiemannRochSpace

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]

open CurveWithOrd CurveDivisor

/-- Riemann's inequality: the index of speciality of any divisor $D$ is nonnegative, i.e.
$\dim L(D) \ge \deg D + 1 - g$. -/
theorem riemann_inequality (D : CurveDivisor C) :
    0 ≤ indexOfSpeciality (F := F) (k := k) D :=
  indexOfSpeciality_nonneg D

/-- Membership in the Riemann–Roch space: if a unit $f \in F^\times$ lies in $L(D)$, then the
divisor $(f) + D$ is effective. -/
lemma effective_of_mem_riemannRochSpace (D : CurveDivisor C) (f : Fˣ)
    (hf : (f : F) ∈ riemannRochSpace (k := k) D) :
    (principalDivisor f + D).IsEffective := by
  rw [mem_riemannRochSpace_iff] at hf
  obtain (h0 | ⟨hne, heff⟩) := hf
  · exact absurd h0 f.ne_zero
  · convert heff using 2
    congr 1
    exact Units.ext rfl

/-- If $\dim L(D) \ge 1$, then the Riemann–Roch space contains a nonzero element (chosen here as
a unit of $F$). -/
lemma exists_nonzero_of_divisorDim_pos (D : CurveDivisor C)
    (h : 1 ≤ divisorDim (F := F) (k := k) D) :
    ∃ f : Fˣ, (f : F) ∈ riemannRochSpace (k := k) D := by
  rw [divisorDim_eq_finrank] at h
  haveI : FiniteDimensional k (riemannRochSpace (F := F) (k := k) D) :=
    riemannRochSpace_finiteDimensional D
  have hpos : 0 < Module.finrank k (riemannRochSpace (F := F) (k := k) D) := by omega
  obtain ⟨⟨v, hv⟩, ⟨⟨w, hw⟩, hne⟩⟩ := Module.finrank_pos_iff.mp hpos
  by_cases h0 : v = 0
  · have hne' : w ≠ 0 := by
      intro hw0
      exact hne (Subtype.ext (h0.trans hw0.symm))
    exact ⟨Units.mk0 w hne', hw⟩
  · exact ⟨Units.mk0 v h0, hv⟩

/-- Linearly equivalent divisors have the same index of speciality. Both the degree and the
Riemann–Roch dimension are invariant under linear equivalence. -/
lemma indexOfSpeciality_eq_of_linearlyEquivalent (A B : CurveDivisor C)
    (h : PicardGroup.LinearlyEquivalent (CurveDivisor C)
      (principalDivisors (F := F)) A B) :
    indexOfSpeciality (F := F) (k := k) A =
      indexOfSpeciality (F := F) (k := k) B := by
  obtain ⟨f, hf⟩ := h


  simp only at hf
  have hdeg : degree C A = degree C B := by
    have hpd := degree_principalDivisor (C := C) (F := F) (k := k) f
    have : degree C (principalDivisor f) = degree C A - degree C B := by
      rw [hf, map_sub]
    linarith
  have hdim := divisorDim_eq_of_linearlyEquivalent (F := F) (k := k) A B ⟨f, hf⟩
  unfold indexOfSpeciality
  rw [hdeg, hdim]

/-- For divisors of sufficiently large degree, the index of speciality vanishes: there exists a
constant $c$ such that every divisor with $\deg D \ge c$ satisfies $\dim L(D) = \deg D + 1 - g$.
The proof picks a maximizing divisor $A$ realizing the genus, then transfers the bound to any
$D$ by linear equivalence after using $D - A$ to find an effective shift. -/
theorem riemann_equality_large_degree :
    ∃ c : ℤ, ∀ D : CurveDivisor C,
      degree C D ≥ c →
        indexOfSpeciality (F := F) (k := k) D = 0 := by
  classical

  obtain ⟨A, hA⟩ := genus_eq_degDim_of_max (C := C) (F := F) (k := k)

  have hiA : indexOfSpeciality (F := F) (k := k) A = 0 := by
    unfold indexOfSpeciality; linarith

  set g := genus (C := C) (F := F) (k := k) with g_def
  have hℓA : (divisorDim (F := F) (k := k) A : ℤ) = degree C A + 1 - (g : ℤ) := by linarith

  refine ⟨degree C A + (g : ℤ), fun D hD => ?_⟩

  have hdeg_sub : degree C (D - A) = degree C D - degree C A := map_sub (degree C) D A
  have hbound_DA := genus_bound (F := F) (k := k) (D - A)


  have hℓ_DA_pos : 1 ≤ divisorDim (F := F) (k := k) (D - A) := by omega

  obtain ⟨f, hf_mem⟩ := exists_nonzero_of_divisorDim_pos (D - A) hℓ_DA_pos

  have heff := effective_of_mem_riemannRochSpace (D - A) f hf_mem

  have hDprime_ge_A : A ≤ D + principalDivisor f := by
    rw [CurveDivisor.IsEffective] at heff
    intro P
    have hP := heff P
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply] at hP ⊢
    linarith


  haveI := riemannRochSpace_finiteDimensional (F := F) (k := k) A
  have ⟨hfd_Dprime, hbound_Dprime⟩ :=
    riemannRochSpace_finrank_le_of_le (F := F) (k := k) hDprime_ge_A

  have hdeg_Dprime : degree C (D + principalDivisor f) = degree C D := by
    rw [map_add, degree_principalDivisor, add_zero]

  have hi_Dprime : indexOfSpeciality (F := F) (k := k) (D + principalDivisor f) = 0 := by

    have h_nonneg := indexOfSpeciality_nonneg (F := F) (k := k) (D + principalDivisor f)

    rw [hdeg_Dprime] at hbound_Dprime
    rw [← divisorDim_eq_finrank, ← divisorDim_eq_finrank] at hbound_Dprime
    unfold indexOfSpeciality at h_nonneg ⊢
    rw [hdeg_Dprime] at h_nonneg
    have hg : (genus (C := C) (F := F) (k := k) : ℤ) = (g : ℤ) := by
      exact_mod_cast g_def.symm
    rw [hg] at h_nonneg ⊢
    linarith

  have hlinEquiv : PicardGroup.LinearlyEquivalent (CurveDivisor C)
      (principalDivisors (F := F)) D (D + principalDivisor f) := by
    refine ⟨f⁻¹, ?_⟩
    simp only [principalDivisor_inv]
    abel
  have hi_eq := indexOfSpeciality_eq_of_linearlyEquivalent D
    (D + principalDivisor f) hlinEquiv
  linarith

/-- Riemann's theorem: the index of speciality is always nonnegative and vanishes for divisors of
sufficiently large degree. Equivalently, $\dim L(D) \ge \deg D + 1 - g$ for all $D$, with
equality for $\deg D \gg 0$. -/
theorem riemann_theorem :
    (∀ D : CurveDivisor C, 0 ≤ indexOfSpeciality (F := F) (k := k) D) ∧
    (∃ c : ℤ, ∀ D : CurveDivisor C,
      degree C D ≥ c →
        indexOfSpeciality (F := F) (k := k) D = 0) :=
  ⟨riemann_inequality, riemann_equality_large_degree⟩

end RiemannRochSpace
