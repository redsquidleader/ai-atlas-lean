/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryO
import Atlas.LieGroups.code.TensorHomAxiom

noncomputable section

open Classical

universe uCatO
universe u_V u_M u_P

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def IsDominantWeightLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    WeightLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

def IsDominantWeightBruhat {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    BruhatLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

theorem bruhatLE_implies_weightLE
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (μ wt : Δ.𝔥 →ₗ[R] R)
    (h : BruhatLE rd μ wt) : WeightLE rd μ wt := by
  classical
  unfold BruhatLE at h
  unfold WeightLE PositiveRootData.IsInQPlus
  induction h with
  | refl => exact ⟨fun _ => 0, by simp⟩
  | @tail b c _hab hbc ih =>
    obtain ⟨α, hα_mem, n, _hn_pos, _hpair, hb_eq⟩ := hbc
    obtain ⟨coeff, hcoeff⟩ := ih
    refine ⟨Function.update coeff α (coeff α + n), ?_⟩
    have hcmu : c - μ = (b - μ) + n • α := by
      have hc : c = b + n • α := by rw [hb_eq]; abel
      rw [hc]; abel
    rw [hcmu, hcoeff]
    symm
    have lhs_eq : ∑ β ∈ rd.posRoots, (Function.update coeff α (coeff α + n) β) • β =
        (coeff α + n) • α + ∑ β ∈ rd.posRoots.erase α, coeff β • β := by
      rw [← Finset.add_sum_erase rd.posRoots
          (fun β => (Function.update coeff α (coeff α + n) β) • β) hα_mem]
      congr 1
      · simp [Function.update_self]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_erase] at hx
        rw [Function.update_of_ne hx.1]
    have rhs_eq : (∑ β ∈ rd.posRoots, coeff β • β) + n • α =
        (coeff α + n) • α + ∑ β ∈ rd.posRoots.erase α, coeff β • β := by
      rw [← Finset.add_sum_erase rd.posRoots (fun β => coeff β • β) hα_mem]
      rw [add_nsmul]; abel
    rw [lhs_eq, ← rhs_eq]


theorem PositiveRootData.corootPairing_self_pos
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) :
    rd.corootPairing α α = 2 := rd.corootPairing_self α hα

theorem WeylGroupData.hasReflection_element_ax
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) :
    ∃ s : wg.W,
      ∀ μ : Δ.𝔥 →ₗ[R] R, wg.dualAction s μ = μ - rd.corootPairing μ α • α := by sorry

theorem WeylGroupData.hasReflection_element
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) :
    ∃ s : wg.W,
      ∀ μ : Δ.𝔥 →ₗ[R] R, wg.dualAction s μ = μ - rd.corootPairing μ α • α :=
  wg.hasReflection_element_ax rd α hα

theorem reflection_in_stabilizerModQ_ax
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (s : wg.W)
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
    (hs : ∀ μ : Δ.𝔥 →ₗ[R] R, wg.dualAction s μ = μ - rd.corootPairing μ α • α)
    (lam : Δ.𝔥 →ₗ[R] R) :
    s ∈ WeylStabilizerModQ rd wg lam := by sorry

theorem WeylGroupData.reflection_preserves_stabilizerModQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (s : wg.W)
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
    (hs : ∀ μ : Δ.𝔥 →ₗ[R] R, wg.dualAction s μ = μ - rd.corootPairing μ α • α) :
    ∀ (lam : Δ.𝔥 →ₗ[R] R) (w : wg.W),
      w ∈ WeylStabilizerModQ rd wg lam → s * w ∈ WeylStabilizerModQ rd wg lam := by
  intro lam w hw

  simp only [WeylStabilizerModQ, Set.mem_setOf_eq] at hw ⊢
  obtain ⟨c_w, hc_w⟩ := hw

  have hmul : wg.dualAction (s * w) lam = wg.dualAction s (wg.dualAction w lam) :=
    wg.dualAction_mul s w lam
  rw [hmul, hs (wg.dualAction w lam)]


  have hs_stab := reflection_in_stabilizerModQ_ax wg rd s α hα hs (wg.dualAction w lam)
  simp only [WeylStabilizerModQ, Set.mem_setOf_eq] at hs_stab
  obtain ⟨c_sw, hc_sw⟩ := hs_stab
  rw [hs (wg.dualAction w lam)] at hc_sw


  refine ⟨fun β => c_sw β + c_w β, ?_⟩
  have key : wg.dualAction w lam - rd.corootPairing (wg.dualAction w lam) α • α - lam =
    (wg.dualAction w lam - rd.corootPairing (wg.dualAction w lam) α • α - wg.dualAction w lam) +
    (wg.dualAction w lam - lam) := by abel
  rw [key, hc_sw, hc_w, ← Finset.sum_add_distrib]
  congr 1
  funext β
  rw [add_zsmul]

theorem WeylGroupData.hasReflection
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) :
    ∃ s : wg.W,
      (∀ μ : Δ.𝔥 →ₗ[R] R, wg.dualAction s μ = μ - rd.corootPairing μ α • α) ∧
      (∀ (lam : Δ.𝔥 →ₗ[R] R) (w : wg.W),
        w ∈ WeylStabilizerModQ rd wg lam → s * w ∈ WeylStabilizerModQ rd wg lam) := by
  obtain ⟨s, hs⟩ := wg.hasReflection_element rd α hα
  exact ⟨s, hs, wg.reflection_preserves_stabilizerModQ rd s α hα hs⟩

theorem descentRoot_coxeter_input
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (c : (Δ.𝔥 →ₗ[R] R) → ℕ)
    (hc : lam - wg.dualAction w lam = ∑ α ∈ rd.posRoots, c α • α)
    (hne : wg.dualAction w lam ≠ lam) :
    ∃ (α : Δ.𝔥 →ₗ[R] R) (_ : α ∈ rd.posRoots) (n : ℕ),
      0 < n ∧
      rd.corootPairing (wg.dualAction w lam) α = -↑n ∧
      n ≤ c α := by
  sorry

theorem WeylGroupData.descentRoot
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (hle : WeightLE rd (wg.dualAction w lam) lam)
    (hne : wg.dualAction w lam ≠ lam) :
    ∃ (α : Δ.𝔥 →ₗ[R] R) (_ : α ∈ rd.posRoots) (n : ℕ),
      0 < n ∧
      rd.corootPairing (wg.dualAction w lam) α = -↑n ∧
      WeightLE rd (wg.dualAction w lam + n • α) lam := by

  obtain ⟨c, hc⟩ := hle

  obtain ⟨α, hα, n, hn, hpair, hcn⟩ :=
    descentRoot_coxeter_input rd wg lam w hw c hc hne

  refine ⟨α, hα, n, hn, hpair, ⟨fun β => if β = α then c α - n else c β, ?_⟩⟩


  have hsub : lam - (wg.dualAction w lam + n • α) =
      ∑ x ∈ rd.posRoots, c x • x - n • α := by
    rw [← hc]; abel
  rw [hsub]

  rw [← Finset.add_sum_erase _ _ hα, ← Finset.add_sum_erase _ _ hα]

  have herase : ∀ x ∈ rd.posRoots.erase α,
      (if x = α then c α - n else c x) • x = c x • x := by
    intro x hx; simp [(Finset.mem_erase.mp hx).1]
  rw [Finset.sum_congr rfl herase]

  simp only [ite_true]


  have hkey : c α • α = (c α - n) • α + n • α := by
    rw [← add_nsmul, Nat.sub_add_cancel hcn]
  rw [hkey, add_assoc, add_comm (n • α) _, ← add_assoc, add_sub_cancel_right]

theorem bruhat_one_step_reduction
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (hle : WeightLE rd (wg.dualAction w lam) lam)
    (hne : wg.dualAction w lam ≠ lam) :
    ∃ w' : wg.W,
      w' ∈ WeylStabilizerModQ rd wg lam ∧
      WeightLE rd (wg.dualAction w' lam) lam ∧
      (∃ α, ReflectionLT rd α (wg.dualAction w lam) (wg.dualAction w' lam)) := by

  obtain ⟨α, hα, n, hn_pos, hpair_neg, hle'⟩ :=
    wg.descentRoot rd lam w hw hle hne

  obtain ⟨s, hs_act, hs_stab⟩ := wg.hasReflection rd α hα

  refine ⟨s * w, ?_, ?_, α, ?_⟩
  ·
    exact hs_stab lam w hw
  ·


    rw [wg.dualAction_mul, hs_act, hpair_neg]
    simp only [neg_smul, Nat.cast_smul_eq_nsmul R, sub_neg_eq_add]
    exact hle'
  ·

    unfold ReflectionLT
    refine ⟨hα, n, hn_pos, ?_, ?_⟩
    ·

      rw [wg.dualAction_mul, hs_act, hpair_neg]
      simp only [neg_smul, Nat.cast_smul_eq_nsmul R, sub_neg_eq_add]
      rw [rd.corootPairing_add_left, rd.corootPairing_nsmul_left,
          hpair_neg, rd.corootPairing_self_pos α hα]
      ring
    ·
      rw [wg.dualAction_mul, hs_act, hpair_neg]
      simp only [neg_smul, Nat.cast_smul_eq_nsmul R, sub_neg_eq_add]
      abel

theorem weightLE_antisymm
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a b : Δ.𝔥 →ₗ[R] R)
    (h1 : WeightLE rd a b)
    (h2 : WeightLE rd b a) : a = b := by

  unfold WeightLE at h1 h2
  have h2' : rd.IsInQPlus (-(b - a)) := by rwa [show -(b - a) = a - b from by abel]

  suffices h : b - a = 0 by rw [sub_eq_zero] at h; exact h.symm
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2'
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push Not at hall

    exact hμ (by rw [hc]; exact Finset.sum_eq_zero fun β hβ => by simp [hall β hβ])
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _; rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [Finset.ne_of_mem_erase hγ]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ; omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

theorem reflectionLT_ne
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α μ ν : Δ.𝔥 →ₗ[R] R)
    (h : ReflectionLT rd α μ ν) : μ ≠ ν := by
  obtain ⟨hα, n, hn, _, heq⟩ := h
  intro hμν

  have h_nsmul : (n : ℕ) • α = (0 : Δ.𝔥 →ₗ[R] R) := by
    have h1 : ν - n • α = ν := by rw [← heq]; exact hμν
    have : n • α = ν - ν := by
      calc n • α = ν - (ν - n • α) := by abel
        _ = ν - ν := by rw [h1]
    rwa [sub_self] at this


  have h_neg : (-(n : ℤ)) < 0 := by omega
  exact absurd ⟨fun _ => 0, by
    simp only [zero_nsmul, Finset.sum_const_zero]
    rw [show (-(n : ℤ)) • α = -(n • α) from by rw [neg_zsmul, natCast_zsmul]]
    rw [h_nsmul, neg_zero]⟩ (rd.posRoots_pointed_cone α hα (-(n : ℤ)) h_neg)

lemma reflectionLT_implies_weightLE
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α μ ν : Δ.𝔥 →ₗ[R] R)
    (h : ReflectionLT rd α μ ν) :
    WeightLE rd μ ν := by
  classical
  obtain ⟨hα, n, hn, _, heq⟩ := h

  unfold WeightLE
  rw [heq, show ν - (ν - n • α) = n • α from by abel]

  refine ⟨Function.update (fun _ => 0) α n, ?_⟩
  simp_rw [Function.update_apply]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', hα, ite_true]

lemma weightLE_trans
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a b c : Δ.𝔥 →ₗ[R] R)
    (h1 : WeightLE rd a b)
    (h2 : WeightLE rd b c) :
    WeightLE rd a c :=
  PositiveRootData.IsInQPlus_trans rd c b a h2 h1

lemma weightLE_refl
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a : Δ.𝔥 →ₗ[R] R) :
    WeightLE rd a a := by
  unfold WeightLE
  rw [show a - a = 0 from sub_self a]
  exact PositiveRootData.IsInQPlus_zero rd

theorem weightLE_implies_bruhatLE_in_orbit
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (hle : WeightLE rd (wg.dualAction w lam) lam) :
    BruhatLE rd (wg.dualAction w lam) lam := by
  classical


  let S : wg.W → Finset wg.W := fun v =>
    Finset.univ.filter fun u =>
      WeightLE rd (wg.dualAction v lam) (wg.dualAction u lam) ∧
      WeightLE rd (wg.dualAction u lam) lam

  have hS_self : ∀ v : wg.W, WeightLE rd (wg.dualAction v lam) lam → v ∈ S v := by
    intro v hvle
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨weightLE_refl rd _, hvle⟩

  suffices key : ∀ (n : ℕ) (v : wg.W),
      v ∈ WeylStabilizerModQ rd wg lam →
      WeightLE rd (wg.dualAction v lam) lam →
      (S v).card ≤ n →
      BruhatLE rd (wg.dualAction v lam) lam by
    exact key (S w).card w hw hle le_rfl
  intro n
  induction n with
  | zero =>
    intro v hv hvle hcard

    exfalso
    have : 0 < (S v).card := Finset.card_pos.mpr ⟨v, hS_self v hvle⟩
    omega
  | succ n ih =>
    intro v hv hvle hcard
    by_cases heq : wg.dualAction v lam = lam
    · rw [heq]; exact Relation.ReflTransGen.refl
    · obtain ⟨w', hw'mem, hw'le, α, hstep⟩ :=
        bruhat_one_step_reduction rd wg lam v hv hvle heq
      refine Relation.ReflTransGen.head ⟨α, hstep⟩ ?_
      apply ih w' hw'mem hw'le


      have hstep_wle : WeightLE rd (wg.dualAction v lam) (wg.dualAction w' lam) :=
        reflectionLT_implies_weightLE rd α _ _ hstep
      have hstep_ne : wg.dualAction v lam ≠ wg.dualAction w' lam :=
        reflectionLT_ne rd α _ _ hstep
      have hss : S w' ⊂ S v := by
        constructor
        ·

          intro u hu
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact ⟨weightLE_trans rd _ _ _ hstep_wle hu.1, hu.2⟩
        ·
          intro hsub
          have hv_in_Sw' := hsub (hS_self v hvle)
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv_in_Sw'


          exact hstep_ne (weightLE_antisymm rd _ _ hstep_wle hv_in_Sw'.1)

      exact Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (Finset.card_lt_card hss) hcard)

theorem dominantLE_implies_dominantBruhat
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (h : IsDominantWeightLE rd wg lam) : IsDominantWeightBruhat rd wg lam := by
  intro w hw hBruhat


  have hle : WeightLE rd lam (wg.dualAction w lam) :=
    bruhatLE_implies_weightLE _ _ hBruhat
  exact h w hw hle

theorem dominance_equivalence
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) :
    IsDominantWeightLE rd wg lam ↔ IsDominantWeightBruhat rd wg lam := by
  constructor
  ·
    exact dominantLE_implies_dominantBruhat rd wg lam
  ·


    intro hBruhat w hw hle


    set μ := wg.dualAction w lam with hμ_def

    have hw_inv : w⁻¹ ∈ WeylStabilizerModQ rd wg μ := by
      obtain ⟨c, hc⟩ := hw
      refine ⟨fun α => -c α, ?_⟩
      have cancel : wg.dualAction w⁻¹ μ = lam := by
        rw [hμ_def, wg.dualAction_inv_cancel_left]
      rw [cancel]
      have : μ - lam = ∑ α ∈ rd.posRoots, c α • α := by rw [hμ_def]; exact hc
      rw [show lam - μ = -(μ - lam) from by abel, this]
      rw [← Finset.sum_neg_distrib]
      congr 1
      ext α
      simp

    have hle' : WeightLE rd (wg.dualAction w⁻¹ μ) μ := by
      rwa [wg.dualAction_inv_cancel_left]

    have hBr : BruhatLE rd (wg.dualAction w⁻¹ μ) μ :=
      weightLE_implies_bruhatLE_in_orbit rd wg μ w⁻¹ hw_inv hle'

    rw [wg.dualAction_inv_cancel_left] at hBr

    exact hBruhat w hw hBr

def NotNegIntCorootPairing
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, ¬ ∃ n : ℤ, n < 0 ∧ lam (rs.coroot α) = (n : R)

def IsIntegralDominantWeightBruhat
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → BruhatLE rd (wg.dualAction w lam) lam

def IsIntegralDominantWeightLE
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → WeightLE rd (wg.dualAction w lam) lam

theorem integralDominance_equivalence
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) :
    IsIntegralDominantWeightBruhat rd wg lam ↔ IsIntegralDominantWeightLE rd wg lam := by
  constructor
  · intro h w hw; exact bruhatLE_implies_weightLE _ _ (h w hw)
  · intro h w hw; exact weightLE_implies_bruhatLE_in_orbit rd wg lam w hw (h w hw)

theorem coxeter_descent_root_exists
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (hne : wg.dualAction w lam ≠ lam) :
    ∃ (α : Δ.𝔥 →ₗ[R] R) (_ : α ∈ rd.posRoots) (n : ℕ),
      0 < n ∧ rd.corootPairing (wg.dualAction w lam) α = -↑n := by
  sorry

theorem coxeter_orbit_ascent
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hdom : IsDominantWeightLE rd wg lam)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (hne : wg.dualAction w lam ≠ lam) :
    ∃ w' : wg.W,
      w' ∈ WeylStabilizerModQ rd wg lam ∧
      (∃ α, ReflectionLT rd α (wg.dualAction w lam) (wg.dualAction w' lam)) := by

  obtain ⟨α, hα, n, hn_pos, hpair_neg⟩ := coxeter_descent_root_exists rd wg lam w hw hne

  obtain ⟨s, hs_act, hs_stab⟩ := wg.hasReflection rd α hα

  refine ⟨s * w, ?_, α, ?_⟩
  ·
    exact hs_stab lam w hw
  ·
    unfold ReflectionLT
    refine ⟨hα, n, hn_pos, ?_, ?_⟩
    ·


      rw [wg.dualAction_mul, hs_act, hpair_neg]
      simp only [neg_smul, Nat.cast_smul_eq_nsmul R, sub_neg_eq_add]
      rw [rd.corootPairing_add_left, rd.corootPairing_nsmul_left,
          hpair_neg, rd.corootPairing_self_pos α hα]
      ring
    ·
      rw [wg.dualAction_mul, hs_act, hpair_neg]
      simp only [neg_smul, Nat.cast_smul_eq_nsmul R, sub_neg_eq_add]
      abel

theorem dominantLE_implies_integralDominantLE
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (h : IsDominantWeightLE rd wg lam) :
    IsIntegralDominantWeightLE rd wg lam := by


  classical


  let S : wg.W → Finset wg.W := fun v =>
    Finset.univ.filter fun u =>
      WeightLE rd (wg.dualAction v lam) (wg.dualAction u lam)

  have hS_self : ∀ v : wg.W, v ∈ S v := by
    intro v
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact weightLE_refl rd _

  suffices key : ∀ (n : ℕ) (v : wg.W),
      v ∈ WeylStabilizerModQ rd wg lam →
      (S v).card ≤ n →
      WeightLE rd (wg.dualAction v lam) lam by
    intro w hw
    exact key (S w).card w hw le_rfl
  intro n
  induction n with
  | zero =>
    intro v _ hcard

    exfalso
    have : 0 < (S v).card := Finset.card_pos.mpr ⟨v, hS_self v⟩
    omega
  | succ n ih =>
    intro v hv hcard
    by_cases heq : wg.dualAction v lam = lam
    ·
      rw [heq]; exact weightLE_refl rd _
    ·
      obtain ⟨w', hw'mem, α, hstep⟩ :=
        coxeter_orbit_ascent rd wg lam h v hv heq

      have hstep_wle : WeightLE rd (wg.dualAction v lam) (wg.dualAction w' lam) :=
        reflectionLT_implies_weightLE rd α _ _ hstep
      have hstep_ne : wg.dualAction v lam ≠ wg.dualAction w' lam :=
        reflectionLT_ne rd α _ _ hstep

      have hss : S w' ⊂ S v := by
        constructor
        ·

          intro u hu
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact weightLE_trans rd _ _ _ hstep_wle hu
        ·
          intro hsub
          have hv_in_Sw' := hsub (hS_self v)
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv_in_Sw'


          exact hstep_ne (weightLE_antisymm rd _ _ hstep_wle hv_in_Sw')

      have hw'le := ih w' hw'mem (Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (Finset.card_lt_card hss) hcard))

      exact weightLE_trans rd _ _ _ hstep_wle hw'le

theorem dominantBruhat_implies_integralDominantBruhat
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (h : IsDominantWeightBruhat rd wg lam) :
    IsIntegralDominantWeightBruhat rd wg lam := by


  have h1 : IsDominantWeightLE rd wg lam := (dominance_equivalence rd wg lam).mpr h
  have h2 : IsIntegralDominantWeightLE rd wg lam := dominantLE_implies_integralDominantLE rd wg lam h1
  exact (integralDominance_equivalence rd wg lam).mpr h2

theorem neg_zsmul_posRoot_not_in_QPlus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α : Δ.𝔥 →ₗ[R] R)
    (hα : α ∈ rd.posRoots)
    (n : ℤ) (hn : n < 0) :
    ¬ rd.IsInQPlus (n • α) := by

  intro ⟨c, hc⟩
  exact rd.posRoots_pointed_cone α hα n hn ⟨c, hc⟩

theorem stabilizer_roots_form_root_system
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    IsRootSubsystem rd wg rs (rootsOfStabilizer rd wg rs x) :=
  Wx_roots_form_root_system rd wg rs x

theorem stabilizer_is_weyl_group
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :

    (∀ w ∈ WeylStabilizerModQ rd wg x,
      ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
        (∀ i, αs i ∈ rootsOfStabilizer rd wg rs x) ∧
        w = (List.ofFn (fun i => rs.reflection (αs i))).prod) ∧

    (∀ α, α ∈ rootsOfStabilizer rd wg rs x →
       rs.reflection α ∈ WeylStabilizerModQ rd wg x) :=
  Wx_is_weyl_group_of_Rx rd wg rs x

theorem stabilizer_dual_root_subsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    ∀ h : Δ.𝔥,
      h ∈ corootsOf rs (rootsOfStabilizer rd wg rs x) ↔
        (h ∈ Submodule.span ℤ (corootsOf rs (rootsOfStabilizer rd wg rs x)) ∧
         h ∈ corootsOf rs (↑rs.allRoots : Set (Δ.𝔥 →ₗ[R] R))) :=
  Rx_dual_is_root_subsystem rd wg rs x

theorem proposition_15_12
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :

    ((∀ w ∈ WeylStabilizerModQ rd wg x,
      ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
        (∀ i, αs i ∈ rootsOfStabilizer rd wg rs x) ∧
        w = (List.ofFn (fun i => rs.reflection (αs i))).prod) ∧
    (∀ α, α ∈ rootsOfStabilizer rd wg rs x →
       rs.reflection α ∈ WeylStabilizerModQ rd wg x)) ∧

    IsRootSubsystem rd wg rs (rootsOfStabilizer rd wg rs x) ∧

    (∀ h : Δ.𝔥,
      h ∈ corootsOf rs (rootsOfStabilizer rd wg rs x) ↔
        (h ∈ Submodule.span ℤ (corootsOf rs (rootsOfStabilizer rd wg rs x)) ∧
         h ∈ corootsOf rs (↑rs.allRoots : Set (Δ.𝔥 →ₗ[R] R)))) := by
  exact ⟨stabilizer_is_weyl_group rd wg rs x,
         stabilizer_roots_form_root_system rd wg rs x,
         stabilizer_dual_root_subsystem rd wg rs x⟩

lemma pairing_integral_of_WeylStabilizerModQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (α : Δ.𝔥 →ₗ[R] R)
    (hα_pos : α ∈ rd.posRoots)
    (hs : rs.reflection α ∈ WeylStabilizerModQ rd wg lam) :
    ∃ (n : ℤ), (wg.dualAction w lam) (rs.coroot α) = (n : R) := by

  have hα_all : α ∈ rs.allRoots := rs.posRoots_sub α hα_pos
  have hsw_mem : rs.reflection α * w ∈ WeylStabilizerModQ rd wg lam :=
    WeylStabilizerModQ_mul_closed rd wg rs lam hs hw

  obtain ⟨c₁, hc₁⟩ := hw
  obtain ⟨c₂, hc₂⟩ := hsw_mem

  have hmul : wg.dualAction (rs.reflection α * w) lam =
    wg.dualAction (rs.reflection α) (wg.dualAction w lam) :=
    rs.dualAction_mul (rs.reflection α) w lam

  set μ := wg.dualAction w lam
  have hrefl : wg.dualAction (rs.reflection α) μ = μ - μ (rs.coroot α) • α :=
    rs.reflection_formula α hα_all μ

  have h1 : (μ - μ (rs.coroot α) • α) - lam =
    ∑ γ ∈ rd.posRoots, c₂ γ • γ := by rw [← hrefl, ← hmul]; exact hc₂
  have h2 : μ - lam = ∑ γ ∈ rd.posRoots, c₁ γ • γ := hc₁
  have hsub_eq : -(μ (rs.coroot α)) • α =
    ∑ γ ∈ rd.posRoots, (c₂ γ - c₁ γ) • γ := by


    have key : (∑ γ ∈ rd.posRoots, c₂ γ • γ) - (∑ γ ∈ rd.posRoots, c₁ γ • γ) =
      -(μ (rs.coroot α)) • α := by
      have habelsub : (μ - μ (rs.coroot α) • α) - lam - (μ - lam) =
        -(μ (rs.coroot α) • α) := by abel
      rw [h1, h2] at habelsub
      rwa [← neg_smul] at habelsub
    rw [← key, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    exact (sub_smul (c₂ γ) (c₁ γ) γ).symm


  exact rs.pairing_integral α hα_all μ ⟨fun γ => c₂ γ - c₁ γ, hsub_eq⟩

theorem exists_reduced_expression_positive_intermediates
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (k : ℕ) (αs : Fin k → Δ.𝔥 →ₗ[R] R)
    (_hαs_root : ∀ i, αs i ∈ rs.allRoots)
    (_hαs_pos : ∀ i, αs i ∈ rd.posRoots)
    (P : (Δ.𝔥 →ₗ[R] R) → Prop)
    (_hαs_P : ∀ i, P (αs i)) :
    ∃ (m : ℕ) (βs : Fin m → Δ.𝔥 →ₗ[R] R),
      (∀ i, βs i ∈ rs.allRoots) ∧
      (∀ i, βs i ∈ rd.posRoots) ∧
      (∀ i, P (βs i)) ∧
      ((List.ofFn (fun i => rs.reflection (βs i))).prod =
        (List.ofFn (fun i => rs.reflection (αs i))).prod) ∧
      (∀ (j : Fin m),
        wg.dualAction
          (List.ofFn (fun i : Fin j.val => rs.reflection (βs ⟨i.val, by omega⟩))).prod
          (βs j) ∈ rd.posRoots) := by
  sorry

lemma IsInQPlus_add
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (μ ν : Δ.𝔥 →ₗ[R] R)
    (hμ : rd.IsInQPlus μ) (hν : rd.IsInQPlus ν) :
    rd.IsInQPlus (μ + ν) := by
  obtain ⟨c₁, hc₁⟩ := hμ
  obtain ⟨c₂, hc₂⟩ := hν
  refine ⟨fun α => c₁ α + c₂ α, ?_⟩
  rw [hc₁, hc₂, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  exact (add_nsmul α (c₁ α) (c₂ α)).symm

lemma nsmul_posRoot_IsInQPlus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (β : Δ.𝔥 →ₗ[R] R) (hβ : β ∈ rd.posRoots) (n : ℕ) :
    rd.IsInQPlus (n • β) := by
  refine ⟨fun γ => if γ = β then n else 0, ?_⟩
  have : ∀ γ ∈ rd.posRoots,
      (if γ = β then n else 0) • γ = if γ = β then n • β else (0 : Δ.𝔥 →ₗ[R] R) := by
    intro γ _
    split_ifs with h
    · subst h; rfl
    · exact zero_nsmul γ
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' rd.posRoots β]
  simp [hβ]

theorem notNegInt_implies_integralDominantLE
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R)
    (h : NotNegIntCorootPairing rd wg rs lam) :
    IsIntegralDominantWeightLE rd wg lam := by

  unfold IsIntegralDominantWeightLE
  intro w hw
  unfold WeightLE

  obtain ⟨n, αs_raw, hαs_raw, hw_eq⟩ := chevalley_shephard_todd_stabilizer rd wg rs lam w hw

  let αs : Fin n → Δ.𝔥 →ₗ[R] R := fun i =>
    if αs_raw i ∈ rd.posRoots then αs_raw i else -(αs_raw i)
  have hαs_pos : ∀ i, αs i ∈ rd.posRoots := by
    intro i
    simp only [αs]
    split_ifs with hp
    · exact hp
    · have hi_all := (hαs_raw i).1
      rcases rs.roots_pos_or_neg (αs_raw i) hi_all with h1 | h1
      · exact absurd h1 hp
      · exact h1
  have hαs_root : ∀ i, αs i ∈ rs.allRoots :=
    fun i => rs.posRoots_sub (αs i) (hαs_pos i)
  have hrefl_eq : ∀ i, rs.reflection (αs i) = rs.reflection (αs_raw i) := by
    intro i
    simp only [αs]
    split_ifs with hp
    · rfl
    · exact rs.reflection_neg (αs_raw i) (hαs_raw i).1
  have hw_eq' : w = (List.ofFn (fun i => rs.reflection (αs i))).prod := by
    rw [hw_eq]; congr 1; ext i; simp [hrefl_eq]

  have hαs_stab : ∀ i, rs.reflection (αs i) ∈ WeylStabilizerModQ rd wg lam := by
    intro i; rw [hrefl_eq]; exact (hαs_raw i).2


  let P : (Δ.𝔥 →ₗ[R] R) → Prop :=
    fun β => rs.reflection β ∈ WeylStabilizerModQ rd wg lam
  have hαs_P : ∀ i, P (αs i) := hαs_stab
  obtain ⟨m, βs, hβs_root, hβs_pos, hβs_P, hβs_prod, hβs_intermed⟩ :=
    exists_reduced_expression_positive_intermediates rd wg rs n αs hαs_root hαs_pos P hαs_P


  have hw_eq_β : w = (List.ofFn (fun i => rs.reflection (βs i))).prod := by
    rw [hw_eq', hβs_prod]


  have hβs_nonneg : ∀ i, ∃ (mk : ℕ), lam (rs.coroot (βs i)) = (mk : R) := by
    intro i
    have hpos_i := hβs_pos i
    have hnotNeg := h (βs i) hpos_i
    have h1_mem : (1 : wg.W) ∈ WeylStabilizerModQ rd wg lam := by
      unfold WeylStabilizerModQ
      simp only [Set.mem_setOf_eq, wg.dualAction_one, sub_self]
      exact ⟨fun _ => 0, by simp⟩
    have hβs_stab_i : rs.reflection (βs i) ∈ WeylStabilizerModQ rd wg lam := hβs_P i
    have hint := pairing_integral_of_WeylStabilizerModQ rd wg rs lam 1 h1_mem
      (βs i) hpos_i hβs_stab_i
    obtain ⟨ni, hni⟩ := hint
    rw [wg.dualAction_one] at hni
    have hge : 0 ≤ ni := by
      by_contra hlt
      push Not at hlt
      exact hnotNeg ⟨ni, hlt, hni⟩
    obtain ⟨mk, rfl⟩ := Int.eq_ofNat_of_zero_le hge
    exact ⟨mk, by exact_mod_cast hni⟩

  rw [hw_eq_β]

  suffices h_ind : ∀ (k : ℕ) (γs : Fin k → Δ.𝔥 →ₗ[R] R),
      (∀ i, γs i ∈ rs.allRoots) →
      (∀ i, γs i ∈ rd.posRoots) →
      (∀ i, ∃ (mk : ℕ), lam (rs.coroot (γs i)) = (mk : R)) →

      (∀ (j : Fin k),
        wg.dualAction
          (List.ofFn (fun i : Fin j.val => rs.reflection (γs ⟨i.val, by omega⟩))).prod
          (γs j) ∈ rd.posRoots) →
      rd.IsInQPlus (lam - wg.dualAction (List.ofFn (fun i => rs.reflection (γs i))).prod lam)
    from h_ind m βs hβs_root hβs_pos hβs_nonneg hβs_intermed
  intro k
  induction k with
  | zero =>
    intro γs _ _ _ _
    simp only [List.ofFn_zero, List.prod_nil, wg.dualAction_one, sub_self]
    exact rd.IsInQPlus_zero
  | succ k ih =>
    intro γs hγs_root hγs_pos hγs_nonneg hγs_intermed

    let init := fun i : Fin k => γs (Fin.castSucc i)
    have hinit_root : ∀ i : Fin k, init i ∈ rs.allRoots :=
      fun i => hγs_root (Fin.castSucc i)
    have hinit_pos : ∀ i : Fin k, init i ∈ rd.posRoots :=
      fun i => hγs_pos (Fin.castSucc i)
    have hinit_nonneg : ∀ i : Fin k, ∃ (mk : ℕ), lam (rs.coroot (init i)) = (mk : R) :=
      fun i => hγs_nonneg (Fin.castSucc i)

    have hinit_intermed : ∀ (j : Fin k),
        wg.dualAction
          (List.ofFn (fun i : Fin j.val => rs.reflection (init ⟨i.val, by omega⟩))).prod
          (init j) ∈ rd.posRoots := by
      intro j
      have hlist_eq : (List.ofFn (fun i : Fin j.val => rs.reflection (init ⟨i.val, by omega⟩))) =
             (List.ofFn (fun i : Fin j.val => rs.reflection (γs ⟨i.val, by omega⟩))) := by
        congr 1
      rw [hlist_eq]
      exact hγs_intermed (Fin.castSucc j)


    have h_init := ih init hinit_root hinit_pos hinit_nonneg hinit_intermed

    set last_idx : Fin (k + 1) := Fin.last k with last_idx_def
    have hlist_split :
        List.ofFn (fun i : Fin (k + 1) => rs.reflection (γs i)) =
        List.ofFn (fun i : Fin k => rs.reflection (init i)) ++ [rs.reflection (γs last_idx)] := by
      simp only [List.ofFn_succ_last, init, last_idx]
    rw [hlist_split, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    set w_init := (List.ofFn (fun i : Fin k => rs.reflection (init i))).prod

    rw [wg.dualAction_mul]

    have hαk_all : γs last_idx ∈ rs.allRoots := hγs_root last_idx
    have hrefl_k : wg.dualAction (rs.reflection (γs last_idx)) lam =
        lam - (lam (rs.coroot (γs last_idx))) • γs last_idx :=
      rs.reflection_formula (γs last_idx) hαk_all lam
    rw [hrefl_k]
    rw [rs.dualAction_sub w_init lam ((lam (rs.coroot (γs last_idx))) • γs last_idx)]

    have hdecomp :
        lam - (wg.dualAction w_init lam -
          wg.dualAction w_init ((lam (rs.coroot (γs last_idx))) • γs last_idx)) =
        (lam - wg.dualAction w_init lam) +
          wg.dualAction w_init ((lam (rs.coroot (γs last_idx))) • γs last_idx) := by
      abel
    rw [hdecomp]
    apply IsInQPlus_add
    · exact h_init
    ·
      obtain ⟨nk, hnk⟩ := hγs_nonneg last_idx
      rw [hnk]
      rw [Nat.cast_smul_eq_nsmul R nk (γs last_idx)]
      rw [← Nat.cast_smul_eq_nsmul ℤ nk (γs last_idx)]
      rw [rs.dualAction_zsmul w_init (↑nk : ℤ) (γs last_idx)]
      rw [Nat.cast_smul_eq_nsmul ℤ nk]


      have hγk_pos : wg.dualAction w_init (γs last_idx) ∈ rd.posRoots := by

        have := hγs_intermed last_idx

        convert this using 2
      exact nsmul_posRoot_IsInQPlus rd _ hγk_pos nk

theorem dominance_equivalence_full
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R) :
    (IsIntegralDominantWeightLE rd wg lam ↔ NotNegIntCorootPairing rd wg rs lam) := by
  constructor
  ·


    intro hv
    unfold NotNegIntCorootPairing
    intro α hα_pos ⟨n, hn_neg, hn_eq⟩


    have hα_all : α ∈ rs.allRoots := rs.posRoots_sub α hα_pos

    have hrefl : wg.dualAction (rs.reflection α) lam = lam - (lam (rs.coroot α)) • α :=
      rs.reflection_formula α hα_all lam

    rw [hn_eq] at hrefl


    have hs_in_stab : rs.reflection α ∈ WeylStabilizerModQ rd wg lam := by
      unfold WeylStabilizerModQ
      simp only [Set.mem_setOf_eq]
      refine ⟨fun β => if β = α then -n else 0, ?_⟩
      rw [hrefl]
      simp only [sub_sub_cancel_left]


      have rhs_simp : ∑ x ∈ rd.posRoots, (if x = α then -n else (0 : ℤ)) • x = (-n) • α := by
        have : ∀ x ∈ rd.posRoots,
            (if x = α then -n else (0 : ℤ)) • x = if x = α then (-n) • α else 0 := by
          intro x _
          split_ifs with h
          · subst h; rfl
          · exact zero_zsmul x
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' rd.posRoots α]
        simp [hα_pos]
      rw [rhs_simp]


      rw [Int.cast_smul_eq_zsmul R]
      rw [neg_zsmul]

    have hle := hv (rs.reflection α) hs_in_stab


    unfold WeightLE at hle
    rw [hrefl] at hle

    have hsub : lam - (lam - (↑n : R) • α) = (n : ℤ) • α := by
      rw [sub_sub_cancel]
      exact Int.cast_smul_eq_zsmul R n α
    rw [hsub] at hle


    exact neg_zsmul_posRoot_not_in_QPlus rd α hα_pos n hn_neg hle
  ·
    exact notNegInt_implies_integralDominantLE rd wg rs lam

theorem corollary_16_1
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R) :
    (IsDominantWeightLE rd wg lam ↔ IsDominantWeightBruhat rd wg lam) ∧
    (IsDominantWeightBruhat rd wg lam ↔ NotNegIntCorootPairing rd wg rs lam) ∧
    (NotNegIntCorootPairing rd wg rs lam ↔ IsIntegralDominantWeightBruhat rd wg lam) ∧
    (IsIntegralDominantWeightBruhat rd wg lam ↔ IsIntegralDominantWeightLE rd wg lam) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact dominance_equivalence rd wg lam
  ·
    constructor
    ·
      intro hii
      have hiv := dominantBruhat_implies_integralDominantBruhat rd wg lam hii
      have hv := (integralDominance_equivalence rd wg lam).mp hiv
      exact (dominance_equivalence_full rd wg rs lam).mp hv
    ·
      intro hiii
      have hv := (dominance_equivalence_full rd wg rs lam).mpr hiii

      have hi : IsDominantWeightLE rd wg lam := fun w hw hle =>
        weightLE_antisymm rd _ _ hle (hv w hw)
      exact dominantLE_implies_dominantBruhat rd wg lam hi
  ·
    constructor
    · intro hiii
      exact (dominance_equivalence_full rd wg rs lam).mpr hiii |>
        (integralDominance_equivalence rd wg lam).mpr
    · intro hiv
      exact (integralDominance_equivalence rd wg lam).mp hiv |>
        (dominance_equivalence_full rd wg rs lam).mp
  ·
    exact integralDominance_equivalence rd wg lam

def IsProjectiveInO {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (P : Type uCatO) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hP : IsCategoryO Δ rd P) : Prop :=
  ∀ (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_ : IsCategoryO Δ rd M),
  ∀ (N : Type uCatO) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (_ : IsCategoryO Δ rd N),
  ∀ (f : M →ₗ⁅R, 𝔤⁆ N) (_ : Function.Surjective f)
    (g : P →ₗ⁅R, 𝔤⁆ N),
    ∃ (h : P →ₗ⁅R, 𝔤⁆ M), ∀ p, f (h p) = g p

theorem weight_decomp_component_eq
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hMO : IsCategoryO Δ rd M)
    (μ : Δ.𝔥 →ₗ[R] R)
    (v : M)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), v⁆ = μ h • v)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (y : (Δ.𝔥 →ₗ[R] R) → M)
    (hy_wt : ∀ ν, ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), y ν⁆ = ν h • y ν)
    (hsum : v = ∑ ν ∈ S, y ν) :
    ∑ ν ∈ S.filter (· ≠ μ), y ν = 0 := by
  set w := ∑ ν ∈ S.filter (· ≠ μ), y ν with hw_def

  have hy_mem : ∀ ν, y ν ∈ WeightSpace Δ M ν := fun ν => hy_wt ν

  have hv_mem : v ∈ WeightSpace Δ M μ := hv_wt

  have hfilt : S.filter (· ≠ μ) = S.filter (fun x => ¬(x = μ)) := by
    ext x; simp [ne_eq]

  have hsplit : v = ∑ ν ∈ S.filter (· = μ), y ν + w := by
    rw [hsum, hw_def, hfilt]
    exact (Finset.sum_filter_add_sum_filter_not S (· = μ) y).symm

  have hmu_sum_mem : ∑ ν ∈ S.filter (· = μ), y ν ∈ WeightSpace Δ M μ := by
    apply Submodule.sum_mem
    intro ν hν
    rw [Finset.mem_filter] at hν
    rw [hν.2]; exact hy_mem μ

  have hw_in_mu : w ∈ WeightSpace Δ M μ := by
    have : w = v - ∑ ν ∈ S.filter (· = μ), y ν := by rw [hsplit]; abel
    rw [this]; exact (WeightSpace Δ M μ).sub_mem hv_mem hmu_sum_mem

  have hw_in_sup : w ∈ ⨆ (ν : Δ.𝔥 →ₗ[R] R) (_ : ν ≠ μ), WeightSpace Δ M ν := by
    rw [hw_def]
    apply Submodule.sum_mem _ (fun ν hν => ?_)
    rw [Finset.mem_filter] at hν
    exact Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hν.2 (hy_mem ν))

  have hindep := @weightSpace_iSupIndep R _ 𝔤 _ _ Δ M _ _ _ _
  have hdisjoint := hindep μ
  rw [Submodule.disjoint_def] at hdisjoint
  exact hdisjoint w hw_in_mu hw_in_sup

theorem weight_space_surjective_of_surjective
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    {Y : Type*} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (_hYO : IsCategoryO Δ rd Y)
    (f : X →ₗ⁅R, 𝔤⁆ Y)
    (_hf : Function.Surjective f)
    (μ : Δ.𝔥 →ₗ[R] R)
    (v : Y)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v) :
    ∃ (w : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) ∧
      f w = v := by

  obtain ⟨m, hm⟩ := _hf v

  obtain ⟨S, wv, hdecomp⟩ := _hXO.weight_decomp m

  have hfm : v = ∑ ν ∈ S, (f (wv ν : X)) := by
    rw [← hm, hdecomp, map_sum]

  have hf_wt : ∀ ν, ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), (f (↑(wv ν) : X))⁆ = ν h • f (↑(wv ν)) := by
    intro ν h
    have := (wv ν).property h
    rw [← LieModuleHom.map_lie, this, map_smul]

  have hvanish := weight_decomp_component_eq _hYO μ v hv_wt S
    (fun ν => f (wv ν : X)) hf_wt hfm

  by_cases hμS : μ ∈ S
  ·
    refine ⟨(wv μ : X), (wv μ).property, ?_⟩


    have hsplit := Finset.add_sum_erase S (fun ν => f (↑(wv ν) : X)) hμS


    have herase_eq : S.erase μ = S.filter (· ≠ μ) := by
      ext x; simp [Finset.mem_erase, Finset.mem_filter]; tauto
    rw [herase_eq] at hsplit


    simp only [] at hsplit


    rw [hvanish, add_zero] at hsplit

    rw [hfm, hsplit]
  ·

    have hfilt_eq : S.filter (· ≠ μ) = S := by
      ext x; simp [Finset.mem_filter]
      intro hx heq; exact hμS (heq ▸ hx)
    rw [hfilt_eq] at hvanish


    simp only [] at hvanish
    have hv0 : v = 0 := by rw [hfm, hvanish]
    exact ⟨0, fun h => by simp, by rw [hv0]; simp⟩
lemma root_vec_raises_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
    (μ : Δ.𝔥 →ₗ[R] R) (w : X)
    (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) :
    ∀ (h : Δ.𝔥), ⁅(h : 𝔤), (⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ : X)⁆ =
      (α + μ) h • ⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ := by
  intro h

  have hleibniz := leibniz_lie (h : 𝔤) (↑(rd.posRootVec α hα) : 𝔤) w

  have hroot := rd.posRootVec_weight α hα h

  have hwt := hw_wt h
  rw [hroot, hwt] at hleibniz

  rw [smul_lie, LieModule.lie_smul] at hleibniz

  rw [hleibniz]
  simp only [LinearMap.add_apply]
  rw [← add_smul]

theorem dominant_weight_vectors_are_singular
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (μ : Δ.𝔥 →ₗ[R] R)
    (w : X)
    (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w)
    (hμ_max : ∀ (ν : Δ.𝔥 →ₗ[R] R) (v : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v) →
      rd.IsInQPlus (ν - μ) → ν ≠ μ → v = 0) :
    ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), w⁆ = 0 := by
  intro e

  obtain ⟨c, hc⟩ := rd.npos_span e

  have hew : (⁅(e : 𝔤), w⁆ : X) =
      ∑ x ∈ rd.posRoots.attach, c x.1 x.2 • ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), w⁆ := by
    conv_lhs => rw [show (e : 𝔤) = ∑ x ∈ rd.posRoots.attach,
      c x.1 x.2 • (↑(rd.posRootVec x.1 x.2) : 𝔤) from hc]
    rw [sum_lie]
    congr 1
    ext x
    rw [smul_lie]

  have hzero : ∀ (x : { x // x ∈ rd.posRoots }),
      ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), w⁆ = (0 : X) := by
    intro ⟨α, hα⟩
    apply hμ_max (α + μ)
    · exact root_vec_raises_weight α hα μ w hw_wt
    ·
      show rd.IsInQPlus (α + μ - μ)
      rw [add_sub_cancel_right]
      exact ⟨fun β => if β = α then 1 else 0, by simp [Finset.sum_ite_eq', hα]⟩
    ·
      intro heq
      apply rd.posRoots_ne_zero α hα
      have : α + μ - μ = μ - μ := by rw [heq]
      simp [add_sub_cancel_right, sub_self] at this
      exact this

  rw [hew]
  simp only [hzero, smul_zero, Finset.sum_const_zero]

theorem singular_vector_lift_in_O
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    {Y : Type*} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y)
    (f : X →ₗ⁅R, 𝔤⁆ Y)
    (hf : Function.Surjective f)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hμ_max : ∀ (ν : Δ.𝔥 →ₗ[R] R) (v : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v) →
      rd.IsInQPlus (ν - μ) → ν ≠ μ → v = 0)
    (v : Y)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v)
    (_hv_sing : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) :
    ∃ (w : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), w⁆ = 0) ∧
      f w = v := by

  obtain ⟨w, hw_wt, hw_eq⟩ := weight_space_surjective_of_surjective hXO hYO f hf μ v hv_wt

  have hw_sing := dominant_weight_vectors_are_singular μ w hw_wt hμ_max
  exact ⟨w, hw_wt, hw_sing, hw_eq⟩

lemma IsInQPlus_antisymm_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hpos : rd.IsInQPlus μ)
    (hneg : rd.IsInQPlus (-μ)) :
    μ = 0 := by
  obtain ⟨c, hc⟩ := hpos
  obtain ⟨d, hd⟩ := hneg
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hμ (by rw [hc]; exact Finset.sum_eq_zero fun β hβ => by simp [hall β hβ])
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _; rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [Finset.ne_of_mem_erase hγ]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ; omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

def IsInBlockO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (_wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  IsCategoryO Δ rd M ∧


  ∃ (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R),
    GeneralizedEigenspaceCenter M ueaAct chi = ⊤

theorem block_weight_bound_in_O
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (lam : Δ.𝔥 →ₗ[R] R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hMBlock : IsInBlockO Δ rd wg M lam)
    (ν : Δ.𝔥 →ₗ[R] R)
    (v : M)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v)
    (hv_ne : v ≠ 0)
    (hν_above : rd.IsInQPlus (ν - (lam - wg.ρ))) :
    ∃ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam ∧
      WeightLE rd ν (wg.dualAction w lam - wg.ρ) := by
  sorry

theorem dominant_weight_is_maximal_in_O
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (lam : Δ.𝔥 →ₗ[R] R)
    (hdom : IsDominantWeightLE rd wg lam)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hMBlock : IsInBlockO Δ rd wg M lam) :
    ∀ (ν : Δ.𝔥 →ₗ[R] R) (v : M),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v) →
      rd.IsInQPlus (ν - (lam - wg.ρ)) → ν ≠ (lam - wg.ρ) → v = 0 := by
  intro ν v hv_wt hν_above hν_ne

  by_contra hv_ne


  obtain ⟨w, hw_mem, hν_le_w⟩ := block_weight_bound_in_O lam hMBlock ν v hv_wt hv_ne hν_above

  have hw_dom : WeightLE rd (wg.dualAction w lam) lam :=
    dominantLE_implies_integralDominantLE rd wg lam hdom w hw_mem


  have hν_le_lam : rd.IsInQPlus ((lam - wg.ρ) - ν) := by
    have h1 : rd.IsInQPlus (lam - wg.dualAction w lam) := hw_dom
    have h2 : rd.IsInQPlus ((wg.dualAction w lam - wg.ρ) - ν) := hν_le_w
    have heq : (lam - wg.ρ) - ν =
        (lam - wg.dualAction w lam) + ((wg.dualAction w lam - wg.ρ) - ν) := by
      abel

    rw [heq]
    exact IsInQPlus_add rd _ _ h1 h2


  have hν_eq : ν - (lam - wg.ρ) = 0 :=
    IsInQPlus_antisymm_local rd _ hν_above (by rwa [neg_sub])

  exact hν_ne (sub_eq_zero.mp hν_eq)

theorem surjection_source_in_block_of_verma_target
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hMO : IsCategoryO Δ rd M)
    {N : Type*} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (_hNO : IsCategoryO Δ rd N)
    (f : M →ₗ⁅R, 𝔤⁆ N) (_hf : Function.Surjective f)
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (_g : Mlam →ₗ⁅R, 𝔤⁆ N)
    (_hMlam : IsVermaModule Δ Mlam (lam - wg.ρ)) :
    IsInBlockO Δ rd wg M lam := by


  exact ⟨hMO, sorry⟩


theorem verma_projective_of_dominant_aux
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (lam : Δ.𝔥 →ₗ[R] R)
    (hdom : IsDominantWeightLE rd wg lam)
    (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ))
    (hO : IsCategoryO Δ rd Mlam) :
    IsProjectiveInO rd Mlam hO := by


  intro M _ _ _ _ hMO N _ _ _ _ hNO f hf g


  set v_lam := hMlam.toIsHighestWeightModule.highestWeightVec with hv_lam_def
  set v := g v_lam with hv_def

  have hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = (lam - wg.ρ) h • v := by
    intro h
    rw [hv_def, ← LieModuleHom.map_lie, hMlam.toIsHighestWeightModule.cartan_action h,
        map_smul]

  have hv_sing : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0 := by
    intro e
    rw [hv_def, ← LieModuleHom.map_lie, hMlam.toIsHighestWeightModule.npos_action e,
        map_zero]


  have hMBlock : IsInBlockO Δ rd wg M lam :=
    surjection_source_in_block_of_verma_target Δ rd wg lam hMO hNO f hf g hMlam
  have hμ_max_M := dominant_weight_is_maximal_in_O lam hdom hMBlock

  obtain ⟨w, hw_wt, hw_sing, hw_eq⟩ :=
    singular_vector_lift_in_O hMO hNO f hf (lam - wg.ρ) hμ_max_M v hv_wt hv_sing


  obtain ⟨η, hη⟩ := hMlam.universal_map M w hw_wt hw_sing


  have key : (f.comp η) v_lam = g v_lam := by
    simp only [LieModuleHom.comp_apply]
    rw [hη, hw_eq]
  have h_eq : f.comp η = g := hMlam.universal_unique N (f.comp η) g key
  exact ⟨η, fun p => by
    have := congr_arg (· p) h_eq
    simp only [LieModuleHom.comp_apply] at this
    exact this⟩

theorem verma_projective_of_dominant
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (lam : Δ.𝔥 →ₗ[R] R)
    (hdom : IsDominantWeightLE rd wg lam)
    (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ))
    (hO : IsCategoryO Δ rd Mlam) :
    IsProjectiveInO rd Mlam hO :=
  verma_projective_of_dominant_aux lam hdom hMlam hO

theorem tensorHom_adjunction_data
    {R : Type uCatO} [CommRing R]
    {𝔤 : Type uCatO} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {V : Type uCatO} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [Module.Free R V]

    (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hMO : IsCategoryO Δ rd M)
    (N : Type uCatO) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hNO : IsCategoryO Δ rd N)
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (hf : Function.Surjective f)
    (g : TensorProduct R V P →ₗ⁅R, 𝔤⁆ N) :


    ∃ (W_M : Type uCatO) (_ : AddCommGroup W_M) (_ : Module R W_M)
      (_ : LieRingModule 𝔤 W_M) (_ : LieModule R 𝔤 W_M)
      (_hWMO : IsCategoryO Δ rd W_M)
      (W_N : Type uCatO) (_ : AddCommGroup W_N) (_ : Module R W_N)
      (_ : LieRingModule 𝔤 W_N) (_ : LieModule R 𝔤 W_N)
      (_hWNO : IsCategoryO Δ rd W_N)
      (W_f : W_M →ₗ⁅R, 𝔤⁆ W_N) (_ : Function.Surjective W_f)
      (g' : P →ₗ⁅R, 𝔤⁆ W_N),

      ∀ (h' : P →ₗ⁅R, 𝔤⁆ W_M), (∀ p, W_f (h' p) = g' p) →
        ∃ (h : TensorProduct R V P →ₗ⁅R, 𝔤⁆ M), ∀ x, f (h x) = g x :=
  textbook_axiom_tensorHom_adjunction_data M hMO N hNO f hf g

theorem tensor_product_projective_in_O_of_projective
    {R : Type uCatO} [CommRing R]
    {𝔤 : Type uCatO} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    {V : Type uCatO} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [Module.Free R V]


    (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hMO : IsCategoryO Δ rd M)
    (N : Type uCatO) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hNO : IsCategoryO Δ rd N)
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (hf : Function.Surjective f)
    (g : TensorProduct R V P →ₗ⁅R, 𝔤⁆ N) :
    ∃ (h : TensorProduct R V P →ₗ⁅R, 𝔤⁆ M), ∀ x, f (h x) = g x := by


  obtain ⟨W_M, instACG_WM, instMod_WM, instLRM_WM, instLM_WM, hWMO,
          W_N, instACG_WN, instMod_WN, instLRM_WN, instLM_WN, hWNO,
          W_f, hWf_surj, g', hlift⟩ :=
    tensorHom_adjunction_data (P := P) (V := V) M hMO N hNO f hf g


  obtain ⟨h', hh'⟩ := hPproj W_M hWMO W_N hWNO W_f hWf_surj g'

  exact hlift h' hh'

theorem tensor_projective_in_O_aux
    {R : Type uCatO} [CommRing R]
    {𝔤 : Type uCatO} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    {V : Type uCatO} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [Module.Free R V]

    {VP : Type uCatO} [AddCommGroup VP] [Module R VP]
    [LieRingModule 𝔤 VP] [LieModule R 𝔤 VP]
    (hVPO : IsCategoryO Δ rd VP)
    (tensor_iso : VP ≃ₗ⁅R, 𝔤⁆ TensorProduct R V P) :
    IsProjectiveInO rd VP hVPO := by


  intro M _ _ _ _ hMO N _ _ _ _ hNO f hf g

  let g' : TensorProduct R V P →ₗ⁅R, 𝔤⁆ N := g.comp (tensor_iso.symm : TensorProduct R V P →ₗ⁅R, 𝔤⁆ VP)

  obtain ⟨h', hh'⟩ := tensor_product_projective_in_O_of_projective hPO hPproj M hMO N hNO f hf g'

  let h : VP →ₗ⁅R, 𝔤⁆ M := h'.comp (tensor_iso : VP →ₗ⁅R, 𝔤⁆ TensorProduct R V P)
  refine ⟨h, fun p => ?_⟩


  show f (h' (tensor_iso p)) = g p
  rw [hh']
  show g (tensor_iso.symm (tensor_iso p)) = g p
  simp

theorem tensor_projective_in_O
    {R : Type uCatO} [CommRing R]
    {𝔤 : Type uCatO} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    {V : Type uCatO} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [Module.Free R V]

    {VP : Type uCatO} [AddCommGroup VP] [Module R VP]
    [LieRingModule 𝔤 VP] [LieModule R 𝔤 VP]
    (hVPO : IsCategoryO Δ rd VP)
    (tensor_iso : VP ≃ₗ⁅R, 𝔤⁆ TensorProduct R V P) :
    IsProjectiveInO rd VP hVPO :=
  tensor_projective_in_O_aux hPO hPproj hVPO tensor_iso

theorem exists_dominant_shift_for_element
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (μ : Δ.𝔥 →ₗ[R] R)
    (w : wg.W) :
    ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
      WeightLE rd (wg.dualAction w (μ + (↑N + 1) • wg.ρ)) (μ + (↑N + 1) • wg.ρ) := by

  sorry

theorem exists_dominant_shift
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (μ : Δ.𝔥 →ₗ[R] R) :
    ∃ (N : ℕ), IsDominantWeightLE rd wg (μ + (N + 1) • wg.ρ) := by

  have h_per_element : ∀ w : wg.W, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      WeightLE rd (wg.dualAction w (μ + (↑N + 1) • wg.ρ)) (μ + (↑N + 1) • wg.ρ) :=
    fun w => exists_dominant_shift_for_element μ w

  choose N₀ hN₀ using h_per_element

  use Finset.univ.sup N₀


  intro w _hw hle
  have hdom := hN₀ w (Finset.univ.sup N₀) (Finset.le_sup (Finset.mem_univ w))
  exact weightLE_antisymm rd _ _ hle hdom

theorem verma_module_isCategoryO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hM : IsVermaModule Δ M wt) :
    IsCategoryO Δ rd M := by
  constructor
  ·
    refine ⟨{_hM.highestWeightVec}, ?_⟩
    simp only [Finset.coe_singleton]
    exact _hM.toIsHighestWeightModule.generates
  ·
    have hwd := _hM.toIsHighestWeightModule.weight_decomposition
    intro m
    have hm : m ∈ (⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ : Submodule R M) := by
      rw [hwd]; exact Submodule.mem_top
    rw [Submodule.mem_iSup_iff_exists_finset] at hm
    obtain ⟨s, hms⟩ := hm
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hms
    obtain ⟨v, hv⟩ := hms
    exact ⟨s, fun μ => ⟨(v μ : M), (v μ).prop⟩, hv.symm⟩
  ·
    exact ⟨{wt}, fun μ hμ => ⟨wt, Finset.mem_singleton.mpr rfl,
      _hM.weight_subset_QPlus rd μ hμ⟩⟩


structure LieModule.CompositionSeriesOf
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  length : ℕ
  series : Fin (length + 1) → LieSubmodule R 𝔤 M
  bot : series ⟨0, Nat.zero_lt_succ length⟩ = ⊥
  top : series ⟨length, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤
  strictly_increasing : ∀ i : Fin length, series i.castSucc < series i.succ
  quotients_irreducible : ∀ i : Fin length,
    LieModule.IsIrreducible R 𝔤
      (↥(series i.succ) ⧸ (series i.castSucc).comap (series i.succ).incl)

theorem categoryO_isNoetherian'
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hM : IsCategoryO Δ rd M) :
    IsNoetherian R M := by
  sorry

theorem categoryO_isArtinian
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hM : IsCategoryO Δ rd M) :
    IsArtinian R M := by
  sorry

theorem lieModule_isIrreducible_of_covBy
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {A B : LieSubmodule R 𝔤 M} (hcov : A ⋖ B) :
    LieModule.IsIrreducible R 𝔤 (↥B ⧸ LieSubmodule.comap B.incl A) := by
  set K := LieSubmodule.comap B.incl A
  have hne_top : K ≠ ⊤ := by
    intro h; apply ne_of_lt hcov.lt
    exact le_antisymm hcov.lt.le (fun x hx => by
      have := (h ▸ LieSubmodule.mem_top (R := R) (L := 𝔤) (⟨x, hx⟩ : ↥B) : (⟨x, hx⟩ : ↥B) ∈ K)
      simp at this; exact this)
  haveI : Nontrivial (↥B ⧸ K) := by
    change Nontrivial ((↥B : Type _) ⧸ (K : Submodule R ↥B))
    exact Submodule.Quotient.nontrivial_iff.mpr
      (fun h => hne_top (LieSubmodule.toSubmodule_injective h))
  apply LieModule.IsIrreducible.mk
  intro N hN
  set N' := LieSubmodule.comap (LieSubmodule.Quotient.mk' K) N
  have hK_le_N' : K ≤ N' := by
    intro x hx; show (LieSubmodule.Quotient.mk' K) x ∈ N
    rw [(LieSubmodule.Quotient.mk_eq_zero (N := K)).mpr hx]; exact N.zero_mem
  have hA_le : A ≤ LieSubmodule.map B.incl N' := by
    intro x hx; rw [LieSubmodule.mem_map]
    refine ⟨⟨x, hcov.lt.le hx⟩, hK_le_N' ?_, rfl⟩
    show ⟨x, hcov.lt.le hx⟩ ∈ LieSubmodule.comap B.incl A
    rw [LieSubmodule.mem_comap]; simp [LieSubmodule.incl_apply]; exact hx
  have hle_B : LieSubmodule.map B.incl N' ≤ B := LieSubmodule.map_incl_le
  rcases hcov.eq_or_eq hA_le hle_B with hmapA | hmapB
  ·
    exfalso; apply hN
    have hN'_eq : N' = K := le_antisymm
      (fun x hx => by rw [LieSubmodule.mem_comap]; rw [← hmapA]
                      exact (LieSubmodule.mem_map _).mpr ⟨x, hx, rfl⟩)
      hK_le_N'
    rw [eq_bot_iff]; intro q hq
    obtain ⟨b, rfl⟩ := LieSubmodule.Quotient.surjective_mk' K q
    rw [(LieSubmodule.Quotient.mk_eq_zero (N := K)).mpr (hN'_eq ▸ (hq : b ∈ N'))]
    exact LieSubmodule.zero_mem ⊥
  ·
    have hN'_eq_top : N' = ⊤ := by
      rw [eq_top_iff]; intro ⟨x, hxB⟩ _
      have hx_in_map : x ∈ LieSubmodule.map B.incl N' := hmapB.symm ▸ hxB
      obtain ⟨y, hy, hyx⟩ := (LieSubmodule.mem_map _).mp hx_in_map
      have : y = ⟨x, hxB⟩ := by
        ext; change (y : M) = x; rw [LieSubmodule.incl_eq_val] at hyx; exact hyx
      exact this ▸ hy
    rw [eq_top_iff]; intro q _
    obtain ⟨b, rfl⟩ := LieSubmodule.Quotient.surjective_mk' K q
    show (LieSubmodule.Quotient.mk' K) b ∈ N
    have : b ∈ N' := hN'_eq_top ▸ LieSubmodule.mem_top b
    exact this

theorem categoryO_has_composition_series
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hM : IsCategoryO Δ rd M) :
    Nonempty (LieModule.CompositionSeriesOf rd M) := by

  haveI : IsNoetherian R M := categoryO_isNoetherian' _hM
  haveI : IsArtinian R M := categoryO_isArtinian _hM

  haveI : WellFoundedLT (LieSubmodule R 𝔤 M) := LieSubmodule.wellFoundedLT_of_isArtinian R 𝔤 M
  haveI : WellFoundedGT (LieSubmodule R 𝔤 M) := LieSubmodule.wellFoundedGT_of_noetherian R 𝔤 M

  obtain ⟨a, ha_min, n, ha_max, ha_cov⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (LieSubmodule R 𝔤 M)
  have ha0 : a 0 = ⊥ := isMin_iff_eq_bot.mp ha_min
  have han : a n = ⊤ := isMax_iff_eq_top.mp ha_max

  exact ⟨{
    length := n
    series := fun i => a i
    bot := by simp [ha0]
    top := by simp [han]
    strictly_increasing := fun i => (ha_cov i i.isLt).lt
    quotients_irreducible := fun i =>
      lieModule_isIrreducible_of_covBy (ha_cov i i.isLt)
  }⟩

section ProdLieModule

variable {R' : Type*} [CommRing R']
  {L' : Type*} [LieRing L'] [LieAlgebra R' L']
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R' M₁]
    [LieRingModule L' M₁] [LieModule R' L' M₁]
    [AddCommGroup M₂] [Module R' M₂]
    [LieRingModule L' M₂] [LieModule R' L' M₂]

noncomputable instance prodLieRingModule : LieRingModule L' (M₁ × M₂) where
  bracket x m := (⁅x, m.1⁆, ⁅x, m.2⁆)
  add_lie x y m := by ext <;> exact add_lie ..
  lie_add x m n := by ext <;> exact lie_add ..
  leibniz_lie x y m := by ext <;> [exact leibniz_lie x y m.1; exact leibniz_lie x y m.2]

noncomputable instance prodLieModule : LieModule R' L' (M₁ × M₂) where
  smul_lie r x m := by ext <;> exact smul_lie ..
  lie_smul r x m := by ext <;> exact lie_smul ..

variable {N' : Type*} [AddCommGroup N'] [Module R' N']
    [LieRingModule L' N'] [LieModule R' L' N']

noncomputable def prodLieModuleHom
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') :
    M₁ × M₂ →ₗ⁅R', L'⁆ N' where
  toFun m := f₁ m.1 + f₂ m.2
  map_add' m n := by simp [map_add, add_add_add_comm]
  map_smul' r m := by simp [map_smul, smul_add]
  map_lie' {x m} := by
    show f₁ ⁅x, m.1⁆ + f₂ ⁅x, m.2⁆ = ⁅x, f₁ m.1 + f₂ m.2⁆
    rw [lie_add, f₁.map_lie, f₂.map_lie]

omit [LieAlgebra R' L'] [LieModule R' L' M₁] [LieModule R' L' M₂] [LieModule R' L' N'] in
@[simp] lemma prodLieModuleHom_apply
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') (m : M₁ × M₂) :
    prodLieModuleHom f₁ f₂ m = f₁ m.1 + f₂ m.2 := rfl

end ProdLieModule

theorem IsProjectiveInO_prod
    {R' : Type uCatO} [CommRing R']
    {𝔤' : Type uCatO} [LieRing 𝔤'] [LieAlgebra R' 𝔤']
    {Δ : TriangularDecomposition R' 𝔤'}
    {rd : PositiveRootData Δ}
    {P₁ : Type uCatO} [AddCommGroup P₁] [Module R' P₁]
    [LieRingModule 𝔤' P₁] [LieModule R' 𝔤' P₁]
    {P₂ : Type uCatO} [AddCommGroup P₂] [Module R' P₂]
    [LieRingModule 𝔤' P₂] [LieModule R' 𝔤' P₂]
    {hP₁O : IsCategoryO Δ rd P₁} {hP₂O : IsCategoryO Δ rd P₂}
    (hP₁ : IsProjectiveInO rd P₁ hP₁O)
    (hP₂ : IsProjectiveInO rd P₂ hP₂O)
    (hProdO : IsCategoryO Δ rd (P₁ × P₂)) :
    IsProjectiveInO rd (P₁ × P₂) hProdO := by

  intro A _ _ _ _ hAO B _ _ _ _ hBO f hf g

  let g₁ : P₁ →ₗ⁅R', 𝔤'⁆ B :=
    { toFun := fun m => g (m, 0)
      map_add' := fun a b => by
        rw [show (a + b, (0 : P₂)) = (a, 0) + (b, 0) from
          Prod.ext rfl (add_zero 0).symm]
        exact map_add g _ _
      map_smul' := fun r m => by
        rw [show (r • m, (0 : P₂)) = r • (m, 0) from
          Prod.ext rfl (smul_zero r).symm]
        exact map_smul g r _
      map_lie' := fun {x m} => by
        rw [show (⁅x, m⁆, (0 : P₂)) = ⁅x, (m, (0 : P₂))⁆ from
          Prod.ext rfl (lie_zero x).symm]
        exact g.map_lie x _ }
  let g₂ : P₂ →ₗ⁅R', 𝔤'⁆ B :=
    { toFun := fun m => g (0, m)
      map_add' := fun a b => by
        rw [show ((0 : P₁), a + b) = (0, a) + (0, b) from
          Prod.ext (add_zero 0).symm rfl]
        exact map_add g _ _
      map_smul' := fun r m => by
        rw [show ((0 : P₁), r • m) = r • (0, m) from
          Prod.ext (smul_zero r).symm rfl]
        exact map_smul g r _
      map_lie' := fun {x m} => by
        rw [show ((0 : P₁), ⁅x, m⁆) = ⁅x, ((0 : P₁), m)⁆ from
          Prod.ext (lie_zero x).symm rfl]
        exact g.map_lie x _ }

  obtain ⟨h₁, hh₁⟩ := hP₁ A hAO B hBO f hf g₁
  obtain ⟨h₂, hh₂⟩ := hP₂ A hAO B hBO f hf g₂

  refine ⟨prodLieModuleHom h₁ h₂, fun p => ?_⟩
  simp only [prodLieModuleHom_apply, map_add, hh₁, hh₂]

  show g (p.1, 0) + g (0, p.2) = g p
  rw [← map_add g]
  congr 1
  ext <;> simp

theorem IsCategoryO_prod
    {R' : Type*} [CommRing R']
    {𝔤' : Type*} [LieRing 𝔤'] [LieAlgebra R' 𝔤']
    {Δ : TriangularDecomposition R' 𝔤'}
    {rd : PositiveRootData Δ}
    {M₁ : Type*} [AddCommGroup M₁] [Module R' M₁]
    [LieRingModule 𝔤' M₁] [LieModule R' 𝔤' M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R' M₂]
    [LieRingModule 𝔤' M₂] [LieModule R' 𝔤' M₂]
    (_hM₁ : IsCategoryO Δ rd M₁) (_hM₂ : IsCategoryO Δ rd M₂) :
    IsCategoryO Δ rd (M₁ × M₂) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨S₁, hS₁⟩ := _hM₁.finitely_generated
    obtain ⟨S₂, hS₂⟩ := _hM₂.finitely_generated

    let inl : M₁ →ₗ⁅R', 𝔤'⁆ (M₁ × M₂) :=
      { toFun := fun m => (m, 0)
        map_add' := fun a b => by ext <;> simp
        map_smul' := fun r m => by ext <;> simp
        map_lie' := fun {x m} => by
          show (⁅x, m⁆, (0 : M₂)) = (⁅x, m⁆, ⁅x, (0 : M₂)⁆)
          congr 1; exact (lie_zero x).symm }
    let inr : M₂ →ₗ⁅R', 𝔤'⁆ (M₁ × M₂) :=
      { toFun := fun m => (0, m)
        map_add' := fun a b => by ext <;> simp
        map_smul' := fun r m => by ext <;> simp
        map_lie' := fun {x m} => by
          show ((0 : M₁), ⁅x, m⁆) = (⁅x, (0 : M₁)⁆, ⁅x, m⁆)
          congr 1; exact (lie_zero x).symm }
    let S := S₁.image inl ∪ S₂.image inr
    refine ⟨S, ?_⟩
    rw [eq_top_iff]
    intro ⟨m₁, m₂⟩ _
    have hdecomp : (m₁, m₂) = inl m₁ + inr m₂ := by ext <;> simp [inl, inr]
    rw [hdecomp]
    apply (LieSubmodule.lieSpan R' 𝔤' (↑S : Set (M₁ × M₂))).add_mem
    ·

      have h_comap : LieSubmodule.lieSpan R' 𝔤' (↑S₁ : Set M₁) ≤
          LieSubmodule.comap inl (LieSubmodule.lieSpan R' 𝔤' (↑S : Set (M₁ × M₂))) := by
        rw [LieSubmodule.lieSpan_le]
        intro s hs
        simp only [S]
        apply LieSubmodule.subset_lieSpan
        simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
        left
        exact ⟨s, hs, rfl⟩
      rw [hS₁] at h_comap
      exact h_comap (LieSubmodule.mem_top m₁)
    ·
      have h_comap : LieSubmodule.lieSpan R' 𝔤' (↑S₂ : Set M₂) ≤
          LieSubmodule.comap inr (LieSubmodule.lieSpan R' 𝔤' (↑S : Set (M₁ × M₂))) := by
        rw [LieSubmodule.lieSpan_le]
        intro s hs
        simp only [S]
        apply LieSubmodule.subset_lieSpan
        simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
        right
        exact ⟨s, hs, rfl⟩
      rw [hS₂] at h_comap
      exact h_comap (LieSubmodule.mem_top m₂)

  ·
    intro ⟨m₁, m₂⟩
    obtain ⟨S₁, v₁, hm₁⟩ := _hM₁.weight_decomp m₁
    obtain ⟨S₂, v₂, hm₂⟩ := _hM₂.weight_decomp m₂
    refine ⟨S₁ ∪ S₂, fun μ => ⟨(if μ ∈ S₁ then (v₁ μ : M₁) else 0, if μ ∈ S₂ then (v₂ μ : M₂) else 0), ?_⟩, ?_⟩
    · intro h
      ext
      · show ⁅(↑h : 𝔤'), if μ ∈ S₁ then (v₁ μ : M₁) else 0⁆ =
              μ h • (if μ ∈ S₁ then (v₁ μ : M₁) else 0)
        split_ifs with h1
        · exact (v₁ μ).prop h
        · simp [lie_zero]
      · show ⁅(↑h : 𝔤'), if μ ∈ S₂ then (v₂ μ : M₂) else 0⁆ =
              μ h • (if μ ∈ S₂ then (v₂ μ : M₂) else 0)
        split_ifs with h2
        · exact (v₂ μ).prop h
        · simp [lie_zero]
    · ext
      ·
        show m₁ = (∑ μ ∈ S₁ ∪ S₂, (if μ ∈ S₁ then (v₁ μ : M₁) else 0, if μ ∈ S₂ then (v₂ μ : M₂) else 0)).1
        simp only [Prod.fst_sum]
        rw [hm₁, ← Finset.sum_filter]
        congr 1
        ext x; simp (config := { contextual := true }) [Finset.mem_filter, Finset.mem_union]
      ·
        show m₂ = (∑ μ ∈ S₁ ∪ S₂, (if μ ∈ S₁ then (v₁ μ : M₁) else 0, if μ ∈ S₂ then (v₂ μ : M₂) else 0)).2
        simp only [Prod.snd_sum]
        rw [hm₂, ← Finset.sum_filter]
        congr 1
        ext x; simp (config := { contextual := true }) [Finset.mem_filter, Finset.mem_union]
  ·
    obtain ⟨bds₁, hbds₁⟩ := _hM₁.weight_bound
    obtain ⟨bds₂, hbds₂⟩ := _hM₂.weight_bound
    refine ⟨bds₁ ∪ bds₂, fun μ hμ => ?_⟩


    simp only [weights, Set.mem_setOf_eq] at hμ
    rw [Submodule.ne_bot_iff] at hμ
    obtain ⟨⟨m₁, m₂⟩, hm, hne⟩ := hμ


    have hm₁_wt : m₁ ∈ WeightSpace Δ M₁ μ := by
      intro h
      have := congr_arg Prod.fst (hm h)
      exact this
    have hm₂_wt : m₂ ∈ WeightSpace Δ M₂ μ := by
      intro h
      have := congr_arg Prod.snd (hm h)
      exact this
    have h_or : m₁ ≠ 0 ∨ m₂ ≠ 0 := by
      by_contra h_neg
      push Not at h_neg

      exact hne (Prod.ext h_neg.1 h_neg.2)
    cases h_or with
    | inl hm₁_ne =>
      have hμ₁ : μ ∈ weights Δ M₁ := by
        simp only [weights, Set.mem_setOf_eq]
        rw [Submodule.ne_bot_iff]
        exact ⟨m₁, hm₁_wt, hm₁_ne⟩
      obtain ⟨wt, hwt, hq⟩ := hbds₁ μ hμ₁
      exact ⟨wt, Finset.mem_union_left _ hwt, hq⟩
    | inr hm₂_ne =>
      have hμ₂ : μ ∈ weights Δ M₂ := by
        simp only [weights, Set.mem_setOf_eq]
        rw [Submodule.ne_bot_iff]
        exact ⟨m₂, hm₂_wt, hm₂_ne⟩
      obtain ⟨wt, hwt, hq⟩ := hbds₂ μ hμ₂
      exact ⟨wt, Finset.mem_union_right _ hwt, hq⟩

theorem corollary_16_6_i_hom_nonvanishing
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (μ : Δ.𝔥 →ₗ[R] R)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd wg lam)

    (VP : Type*) [AddCommGroup VP] [Module R VP]
    [LieRingModule 𝔤 VP] [LieModule R 𝔤 VP]
    (_hVPO : IsCategoryO Δ rd VP)

    (_htensor : True)

    (Lμ : Type*) [AddCommGroup Lμ] [Module R Lμ]
    [LieRingModule 𝔤 Lμ] [LieModule R 𝔤 Lμ]
    (_hLμ : IsHighestWeightModule Δ Lμ μ)
    (_hLμO : IsCategoryO Δ rd Lμ) :
    ∃ (f : VP →ₗ⁅R, 𝔤⁆ Lμ), f ≠ 0 := by


  sorry

theorem corollary_16_6_i_construction
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (μ : Δ.𝔥 →ₗ[R] R)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd wg lam) :
    ∃ (V : Type u_V) (_ : AddCommGroup V) (_ : Module R V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule R 𝔤 V)
      (_ : Module.Finite R V),
    ∃ (Mlam : Type u_M) (_ : AddCommGroup Mlam) (_ : Module R Mlam)
      (_ : LieRingModule 𝔤 Mlam) (_ : LieModule R 𝔤 Mlam)
      (_ : IsVermaModule Δ Mlam (lam - wg.ρ)),
    ∃ (VP : Type u_P) (_ : AddCommGroup VP) (_ : Module R VP)
      (_ : LieRingModule 𝔤 VP) (_ : LieModule R 𝔤 VP)
      (hVPO : IsCategoryO Δ rd VP),
      IsProjectiveInO rd VP hVPO ∧
      ∀ (Lμ : Type*) [AddCommGroup Lμ] [Module R Lμ]
        [LieRingModule 𝔤 Lμ] [LieModule R 𝔤 Lμ],
        IsHighestWeightModule Δ Lμ μ →
        IsCategoryO Δ rd Lμ →
        ∃ (f : VP →ₗ⁅R, 𝔤⁆ Lμ), f ≠ 0 := by


  sorry

theorem categoryO_enough_projectives_aux
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    ∃ (P : Type*) (_ : AddCommGroup P) (_ : Module R P)
      (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P)
      (hPO : IsCategoryO Δ rd P),
      IsProjectiveInO rd P hPO ∧
      ∃ (f : P →ₗ⁅R, 𝔤⁆ M), Function.Surjective f := by

  obtain ⟨cs⟩ := categoryO_has_composition_series hM


  have top_eq_bot_of_len_zero : cs.length = 0 →
      (⊤ : LieSubmodule R 𝔤 M) = ⊥ := by
    intro hlen
    have h1 := cs.bot
    have h2 := cs.top
    simp only [hlen] at h1 h2
    rw [← h2, ← h1]


  sorry

theorem corollary_16_6_i
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (μ : Δ.𝔥 →ₗ[R] R) :

    ∃ (lam : Δ.𝔥 →ₗ[R] R),
      IsDominantWeightLE rd wg lam ∧

    ∃ (V : Type u_V) (_ : AddCommGroup V) (_ : Module R V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule R 𝔤 V)
      (_ : Module.Finite R V),

    ∃ (Mlam : Type u_M) (_ : AddCommGroup Mlam) (_ : Module R Mlam)
      (_ : LieRingModule 𝔤 Mlam) (_ : LieModule R 𝔤 Mlam)
      (_ : IsVermaModule Δ Mlam (lam - wg.ρ)),

    ∃ (VP : Type u_P) (_ : AddCommGroup VP) (_ : Module R VP)
      (_ : LieRingModule 𝔤 VP) (_ : LieModule R 𝔤 VP)
      (hVPO : IsCategoryO Δ rd VP),

      IsProjectiveInO rd VP hVPO ∧


      ∀ (Lμ : Type*) [AddCommGroup Lμ] [Module R Lμ]
        [LieRingModule 𝔤 Lμ] [LieModule R 𝔤 Lμ],
        IsHighestWeightModule Δ Lμ μ →
        IsCategoryO Δ rd Lμ →
        ∃ (f : VP →ₗ⁅R, 𝔤⁆ Lμ), f ≠ 0 := by

  obtain ⟨N, hN_dom⟩ := exists_dominant_shift μ (wg := wg)

  set lam := μ + (↑N + 1) • wg.ρ with lam_def

  refine ⟨lam, hN_dom, ?_⟩


  exact corollary_16_6_i_construction μ lam hN_dom

theorem categoryO_enough_projectives
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    ∃ (P : Type*) (_ : AddCommGroup P) (_ : Module R P)
      (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P)
      (hPO : IsCategoryO Δ rd P),
      IsProjectiveInO rd P hPO ∧
      ∃ (f : P →ₗ⁅R, 𝔤⁆ M), Function.Surjective f :=
  categoryO_enough_projectives_aux (wg := wg) hM


theorem indecomposable_projective_infrastructure
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    Nontrivial P ∧ IsNoetherian R P ∧
    (∀ (Q₁ Q₂ : LieSubmodule R 𝔤 P), Q₁ ≠ ⊤ → Q₂ ≠ ⊤ → Q₁ ⊔ Q₂ ≠ ⊤) := by sorry

theorem indecomposable_projective_nontrivial
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    (_hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    Nontrivial P :=
  (indecomposable_projective_infrastructure _hPO _hPproj _hindec).1

theorem proper_join_of_indecomposable_projective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    (_hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (Q₁ Q₂ : LieSubmodule R 𝔤 P)
    (_hQ₁ : Q₁ ≠ ⊤) (_hQ₂ : Q₂ ≠ ⊤) :
    Q₁ ⊔ Q₂ ≠ ⊤ :=
  (indecomposable_projective_infrastructure _hPO _hPproj _hindec).2.2 Q₁ Q₂ _hQ₁ _hQ₂

theorem categoryO_isNoetherian
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P) :
    IsNoetherian R P :=
  categoryO_isNoetherian' _hPO

theorem indecomposable_projective_has_greatest_proper_submodule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    ∃ (J : LieSubmodule R 𝔤 P), J ≠ ⊤ ∧
      ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J := by


  haveI hNoeth : IsNoetherian R P := categoryO_isNoetherian hPO

  have hwfgt : WellFoundedGT (LieSubmodule R 𝔤 P) :=
    LieSubmodule.wellFoundedGT_of_noetherian R 𝔤 P

  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwfgt


  have hbot_ne_top : (⊥ : LieSubmodule R 𝔤 P) ≠ ⊤ := by

    haveI : Nontrivial P := indecomposable_projective_nontrivial hPO hPproj hindec
    haveI : Nontrivial (LieSubmodule R 𝔤 P) :=
      (LieSubmodule.nontrivial_iff R 𝔤 P).mpr inferInstance
    exact bot_ne_top


  have hsSup : sSup {N : LieSubmodule R 𝔤 P | N ≠ ⊤} ≠ ⊤ := by
    have hsc := hwfgt {N : LieSubmodule R 𝔤 P | N ≠ ⊤}
      ⟨⊥, hbot_ne_top⟩
      (fun a ha b hb => proper_join_of_indecomposable_projective hPO hPproj hindec a b ha hb)
    exact hsc
  exact ⟨sSup {N | N ≠ ⊤}, hsSup, fun N hN => le_sSup hN⟩


theorem projective_cover_unique_simple_quotient_aux
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    ∃ (J : LieSubmodule R 𝔤 P), J ≠ ⊤ ∧
      (∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J) ∧
      LieModule.IsIrreducible R 𝔤 (P ⧸ J) := by


  have ⟨J, hJ_ne_top, hJ_max⟩ : ∃ (J : LieSubmodule R 𝔤 P), J ≠ ⊤ ∧
      ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J := by


    exact indecomposable_projective_has_greatest_proper_submodule hPO hPproj hindec

  have hJcoatom : IsCoatom J :=
    ⟨hJ_ne_top, fun K hJK => by
      by_contra hK; exact lt_irrefl J (lt_of_lt_of_le hJK (hJ_max K hK))⟩


  have hIrr : LieModule.IsIrreducible R 𝔤 (P ⧸ J) := by
    haveI : Nontrivial (LieSubmodule R 𝔤 (P ⧸ J)) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro h; apply hJcoatom.1; rw [eq_top_iff]; intro p _
      have := (show LieSubmodule.Quotient.mk' J p ∈ (⊤ : LieSubmodule R 𝔤 (P ⧸ J))
        from LieSubmodule.mem_top _)
      rw [← h] at this; simp [LieSubmodule.mem_bot] at this; exact this
    exact {
      eq_bot_or_eq_top := by
        intro N

        set N' := LieSubmodule.comap (LieSubmodule.Quotient.mk' J) N

        have hJ_le_N' : J ≤ N' := by
          intro x hx; show (LieSubmodule.Quotient.mk' J) x ∈ N
          rw [(LieSubmodule.Quotient.mk_eq_zero J).mpr hx]; exact N.zero_mem

        rcases eq_or_lt_of_le hJ_le_N' with hJN | hJN
        · left; rw [eq_bot_iff]; intro x hx
          obtain ⟨p, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
          simp only [LieSubmodule.mem_bot]; rw [LieSubmodule.Quotient.mk_eq_zero]
          exact hJN ▸ (hx : p ∈ N')
        · right; rw [eq_top_iff]; intro x _
          obtain ⟨p, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
          exact (show p ∈ N' from by rw [hJcoatom.2 N' hJN]; exact LieSubmodule.mem_top _)
    }
  exact ⟨J, hJ_ne_top, hJ_max, hIrr⟩

theorem projective_cover_unique_simple_quotient
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    ∃ (J : LieSubmodule R 𝔤 P), J ≠ ⊤ ∧
      (∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J) ∧
      LieModule.IsIrreducible R 𝔤 (P ⧸ J) :=
  projective_cover_unique_simple_quotient_aux hPO hPproj hindec


theorem projective_hom_finiteDimensional
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    Module.Finite R (P →ₗ⁅R, 𝔤⁆ M) := by sorry

theorem CategoryO.block_decomposition_with_characters
    [IsNoetherianRing R]
    {Δ : TriangularDecomposition R 𝔤}
    [Module.Free R Δ.𝔥] [Module.Finite R Δ.𝔥]
    {rd : PositiveRootData Δ}
    (wg : WeylGroupData Δ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :
    ∃ (n : ℕ)
      (chis : Fin n → (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R))
      (N : Fin n → LieSubmodule R 𝔤 M),

      (∀ i j, i ≠ j → Disjoint (N i) (N j)) ∧

      (⨆ i, N i) = ⊤ ∧

      (∀ i, (N i : Submodule R M) =
        GeneralizedEigenspaceCenter M
          (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M))
          (chis i)) := by

  let ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M :=
    UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)
  have hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
    intro x m
    simp [ueaAct, LieModule.toEnd_apply_apply]

  exact CategoryO.infinitesimalCharacter_decomposition wg hM ueaAct hcompat


def LieModule.CompositionSeriesOf.countFactorsIso
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs : LieModule.CompositionSeriesOf rd M)
    (L : Type*) [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] : ℕ :=
  Finset.card (Finset.univ.filter fun (i : Fin cs.length) =>
    Nonempty (L ≃ₗ⁅R, 𝔤⁆ (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl)))

theorem jordanHolder_composition_multiplicity_independent
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs₁ cs₂ : LieModule.CompositionSeriesOf rd M)
    (L : Type*) [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    (_hL : LieModule.IsIrreducible R 𝔤 L) :
    cs₁.countFactorsIso L = cs₂.countFactorsIso L := by sorry

def compositionMultiplicityOfModule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (L : Type*) [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    (_hL : LieModule.IsIrreducible R 𝔤 L) : ℕ :=
  (Classical.choice (categoryO_has_composition_series hM)).countFactorsIso L

noncomputable def quotTopBotLieModuleEquiv
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] :
    (↥(⊤ : LieSubmodule R 𝔤 L) ⧸
      ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl)) ≃ₗ⁅R,𝔤⁆ L := by
  have hbot_sub : ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule = ⊥ := by
    have h : (⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl = ⊥ := by
      rw [LieSubmodule.comap_incl_eq_bot]; simp
    simp [h]
  exact {
    ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule.quotEquivOfEqBot
      hbot_sub |>.trans (LinearEquiv.ofTop (⊤ : Submodule R L) rfl) with
    map_lie' := by
      intro x q
      induction q using Quotient.inductionOn'
      rfl
  }

lemma schur_lie_module_noniso_zero
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (_h1 : LieModule.IsIrreducible R 𝔤 M₁)
    (_h2 : LieModule.IsIrreducible R 𝔤 M₂)
    (_hne : ¬ Nonempty (M₁ ≃ₗ⁅R, 𝔤⁆ M₂)) :
    Module.finrank R (M₁ →ₗ⁅R, 𝔤⁆ M₂) = 0 := by

  have hall_zero : ∀ f : M₁ →ₗ⁅R, 𝔤⁆ M₂, f = 0 := by
    intro f
    by_contra hf
    apply _hne

    have hker : f.ker ≠ ⊤ := by
      intro h
      apply hf
      ext x
      have : x ∈ f.ker := by rw [h]; trivial
      rwa [LieModuleHom.mem_ker] at this

    have hker_bot : f.ker = ⊥ :=
      (_h1.eq_bot_or_eq_top f.ker).resolve_right hker

    have hinj : Function.Injective f := (LieModuleHom.ker_eq_bot f).mp hker_bot

    have hrange_ne_bot : f.range ≠ ⊥ := by
      intro h
      apply hf
      ext x
      have : f x ∈ f.range := ⟨x, rfl⟩
      rw [h] at this
      simp [LieSubmodule.mem_bot] at this
      simp [this]

    have hrange_top : f.range = ⊤ :=
      (_h2.eq_bot_or_eq_top f.range).resolve_left hrange_ne_bot

    have hsurj : Function.Surjective f := (LieModuleHom.range_eq_top f).mp hrange_top

    let e : M₁ ≃ₗ[R] M₂ := LinearEquiv.ofBijective (f : M₁ →ₗ[R] M₂) ⟨hinj, hsurj⟩
    exact ⟨{
      f with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
    }⟩

  haveI : Subsingleton (M₁ →ₗ⁅R, 𝔤⁆ M₂) := ⟨fun a b => by
    rw [hall_zero a, hall_zero b]⟩
  exact Module.finrank_zero_of_subsingleton

lemma lie_endo_is_scalar
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hirr : LieModule.IsIrreducible R 𝔤 M)
    [FiniteDimensional R M]
    (f : M →ₗ⁅R, 𝔤⁆ M) : ∃ c : R, f = c • LieModuleHom.id := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible R 𝔤 M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f : M →ₗ[R] M)
  use c
  set g : M →ₗ⁅R, 𝔤⁆ M := f - c • LieModuleHom.id
  suffices g = 0 by rwa [sub_eq_zero] at this
  have hker_ne_bot : g.ker ≠ ⊥ := by
    rw [Module.End.hasEigenvalue_iff] at hc
    intro h; apply hc; rw [eq_bot_iff]
    intro x hx; rw [Module.End.mem_eigenspace_iff] at hx
    have : x ∈ g.ker := by
      rw [LieModuleHom.mem_ker]
      have : g x = f x - c • x := by
        show (f - c • LieModuleHom.id).toFun x = f x - c • x
        simp [LieModuleHom.sub_apply, LieModuleHom.smul_apply, LieModuleHom.id_apply]
      rw [this]; exact sub_eq_zero.mpr hx
    rw [h] at this; exact this
  ext x
  have hx : x ∈ g.ker := by
    rw [(hirr.eq_bot_or_eq_top g.ker).resolve_left hker_ne_bot]
    exact LieSubmodule.mem_top x
  rwa [LieModuleHom.mem_ker] at hx

lemma schur_lie_module_iso_one
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (_h1 : LieModule.IsIrreducible R 𝔤 M₁)
    (_h2 : LieModule.IsIrreducible R 𝔤 M₂)
    (_hiso : Nonempty (M₁ ≃ₗ⁅R, 𝔤⁆ M₂))
    [FiniteDimensional R M₁] :
    Module.finrank R (M₁ →ₗ⁅R, 𝔤⁆ M₂) = 1 := by
  obtain ⟨σ⟩ := _hiso
  apply finrank_eq_one (σ.toLieModuleHom)
  ·
    intro h
    haveI : Nontrivial M₁ := LieModule.nontrivial_of_isIrreducible R 𝔤 M₁
    obtain ⟨x, hx⟩ := exists_ne (0 : M₁)
    apply hx; apply σ.injective
    have : σ.toLieModuleHom x = 0 := by rw [h]; simp
    rw [show σ x = σ.toLieModuleHom x from rfl, this, map_zero]
  ·
    intro f

    set g : M₁ →ₗ⁅R, 𝔤⁆ M₁ := LieModuleHom.comp σ.symm.toLieModuleHom f

    obtain ⟨c, hc⟩ := lie_endo_is_scalar _h1 g
    use c
    ext x

    have hgx : σ.symm (f x) = c • x := by
      have := congr_arg (· x) hc
      simp [LieModuleHom.smul_apply] at this
      exact this
    have hfx : f x = σ (c • x) := by
      rw [← hgx, LieModuleEquiv.apply_symm_apply]
    rw [LieModuleHom.smul_apply, hfx, map_smul]
    rfl

lemma radical_le_ker_of_hom_to_simple
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L]
    (hL_simple : LieModule.IsIrreducible R 𝔤 L)
    {J : LieSubmodule R 𝔤 P}
    (hJ_proper : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)
    (f : P →ₗ⁅R, 𝔤⁆ L) : J ≤ f.ker := by
  rcases hL_simple.eq_bot_or_eq_top f.range with hrange | hrange
  ·
    have hf0 : f = 0 := by
      ext x
      have hx : f x ∈ f.range := (LieModuleHom.mem_range f (f x)).mpr ⟨x, rfl⟩
      rw [hrange] at hx; simpa [LieSubmodule.mem_bot] using hx
    rw [hf0]; intro x _; simp [LieModuleHom.mem_ker]
  ·

    rcases hL_simple.eq_bot_or_eq_top (LieSubmodule.map f J) with hfJ | hfJ
    ·
      exact (LieModuleHom.le_ker_iff_map J).mpr hfJ
    ·
      exfalso; apply hJ_proper
      ext p; simp only [LieSubmodule.mem_top, iff_true]

      have hfp : f p ∈ LieSubmodule.map f J := hfJ ▸ LieSubmodule.mem_top _
      obtain ⟨j, hj, hjp⟩ := (LieSubmodule.mem_map (f p)).mp hfp

      have hker_ne_top : f.ker ≠ ⊤ := by
        intro hk
        have hf0 : f = 0 := by
          ext x; exact LieModuleHom.mem_ker.mp (hk ▸ LieSubmodule.mem_top x)
        have hrange0 : (0 : P →ₗ⁅R, 𝔤⁆ L).range = ⊥ := by
          ext y; constructor
          · intro hy; rw [LieModuleHom.mem_range] at hy; obtain ⟨a, ha⟩ := hy
            simp at ha; rw [LieSubmodule.mem_bot]; exact ha.symm
          · intro hy; rw [LieSubmodule.mem_bot] at hy; rw [hy]
            rw [LieModuleHom.mem_range]; exact ⟨0, by simp⟩
        rw [hf0, hrange0] at hrange; exact absurd hrange bot_ne_top

      have hker_le := hJ_max f.ker hker_ne_top

      have hpj_ker : p - j ∈ f.ker :=
        LieModuleHom.mem_ker.mpr (by rw [map_sub, hjp, sub_self])
      have : p = j + (p - j) := by abel
      rw [this]; exact J.add_mem hj (hker_le hpj_ker)

noncomputable def LieModuleHom.liftQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (f : P →ₗ⁅R, 𝔤⁆ L) (h : J ≤ f.ker) :
    (P ⧸ J) →ₗ⁅R, 𝔤⁆ L where
  toLinearMap := J.toSubmodule.liftQ f.toLinearMap (by
    intro x hx; exact LinearMap.mem_ker.mpr (LieModuleHom.mem_ker.mp (h hx)))
  map_lie' := by
    intro x m
    induction m using Quotient.inductionOn' with | h m =>
    show f ⁅x, m⁆ = ⁅x, f m⁆
    exact f.map_lie x m

noncomputable def homEquivThroughQuotient
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (hfact : ∀ (f : P →ₗ⁅R, 𝔤⁆ L), J ≤ f.ker) :
    ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) ≃ₗ[R] (P →ₗ⁅R, 𝔤⁆ L) :=
  LinearEquiv.ofBijective
    { toFun := fun g => g.comp (LieSubmodule.Quotient.mk' J)
      map_add' := fun g₁ g₂ => by ext; simp
      map_smul' := fun r g => by ext; simp }
    ⟨by

      intro g₁ g₂ h
      ext ⟨m⟩
      exact LieModuleHom.congr_fun h m
    , by

      intro f
      exact ⟨LieModuleHom.liftQ f (hfact f), by
        ext p; rfl⟩
    ⟩

theorem projective_hom_simple_kronecker_delta
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {J : LieSubmodule R 𝔤 P}
    (hJ_proper : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)

    [FiniteDimensional R (P ⧸ J)]

    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    (hL_simple : LieModule.IsIrreducible R 𝔤 L) :

    (Nonempty (L ≃ₗ⁅R, 𝔤⁆ (P ⧸ J)) →
      Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) = 1) ∧
    (¬ Nonempty (L ≃ₗ⁅R, 𝔤⁆ (P ⧸ J)) →
      Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) = 0) := by

  have hfact : ∀ (f : P →ₗ⁅R, 𝔤⁆ L), J ≤ f.ker :=
    fun f => radical_le_ker_of_hom_to_simple hL_simple hJ_proper hJ_max f

  have hequiv : ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) ≃ₗ[R] (P →ₗ⁅R, 𝔤⁆ L) :=
    homEquivThroughQuotient hfact

  have hJcoatom : IsCoatom J :=
    ⟨hJ_proper, fun K hJK => by
      by_contra hK
      exact lt_irrefl J (lt_of_lt_of_le hJK (hJ_max K hK))⟩
  have hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J) := by
    haveI : Nontrivial (LieSubmodule R 𝔤 (P ⧸ J)) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro h
      apply hJcoatom.1
      rw [eq_top_iff]
      intro p _
      have := (show LieSubmodule.Quotient.mk' J p ∈ (⊤ : LieSubmodule R 𝔤 (P ⧸ J))
        from LieSubmodule.mem_top _)
      rw [← h] at this
      simp [LieSubmodule.mem_bot] at this
      exact this
    exact {
      eq_bot_or_eq_top := by
        intro N
        set N' := LieSubmodule.comap (LieSubmodule.Quotient.mk' J) N
        have hJ_le_N' : J ≤ N' := by
          intro x hx
          show (LieSubmodule.Quotient.mk' J) x ∈ N
          rw [(LieSubmodule.Quotient.mk_eq_zero J).mpr hx]
          exact N.zero_mem
        rcases eq_or_lt_of_le hJ_le_N' with hJN | hJN
        · left
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨p, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
          simp only [LieSubmodule.mem_bot]
          rw [LieSubmodule.Quotient.mk_eq_zero]
          exact hJN ▸ (hx : p ∈ N')
        · right
          rw [eq_top_iff]
          intro x _
          obtain ⟨p, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
          exact (show p ∈ N' from by rw [hJcoatom.2 N' hJN]; exact LieSubmodule.mem_top _)
    }

  have hfinrank : Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) =
      Module.finrank R ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) :=
    (hequiv.finrank_eq).symm

  constructor
  ·
    intro ⟨iso⟩
    rw [hfinrank]

    exact schur_lie_module_iso_one hPJ_irr hL_simple ⟨iso.symm⟩
  ·
    intro hne
    rw [hfinrank]

    have hne' : ¬ Nonempty ((P ⧸ J) ≃ₗ⁅R, 𝔤⁆ L) := by
      intro ⟨iso⟩; exact hne ⟨iso.symm⟩
    exact schur_lie_module_noniso_zero hPJ_irr hL_simple hne'

theorem hom_fin_and_finrank_additive_over_composition_series
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs : LieModule.CompositionSeriesOf rd M) :
    Module.Finite R (P →ₗ⁅R, 𝔤⁆ M) ∧
    Module.finrank R (P →ₗ⁅R, 𝔤⁆ M) =
      ∑ i : Fin cs.length,
        Module.finrank R (P →ₗ⁅R, 𝔤⁆
          (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl)) := by sorry

theorem hom_finrank_additive_over_composition_series
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs : LieModule.CompositionSeriesOf rd M) :
    Module.finrank R (P →ₗ⁅R, 𝔤⁆ M) =
      ∑ i : Fin cs.length,
        Module.finrank R (P →ₗ⁅R, 𝔤⁆
          (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl)) :=
  (hom_fin_and_finrank_additive_over_composition_series _hPO _hPproj cs).2

theorem compositionFactor_isCategoryO
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (cs : LieModule.CompositionSeriesOf rd M)
    (i : Fin cs.length) :
    IsCategoryO Δ rd
      (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl) :=
  IsCategoryO_quotient (IsCategoryO_lieSubmodule hM (cs.series i.succ))
    ((cs.series i.castSucc).comap (cs.series i.succ).incl)

theorem irreducible_in_categoryO_finiteDimensional
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hMO : IsCategoryO Δ rd M)
    (_hM_irr : LieModule.IsIrreducible R 𝔤 M) :
    FiniteDimensional R M := by sorry

theorem compositionFactor_finiteDimensional
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (cs : LieModule.CompositionSeriesOf rd M)
    (i : Fin cs.length) :
    FiniteDimensional R
      (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl) :=
  irreducible_in_categoryO_finiteDimensional
    (compositionFactor_isCategoryO hM cs i)
    (cs.quotients_irreducible i)

theorem quotient_by_radical_finiteDimensional
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    {J : LieSubmodule R 𝔤 P}
    (_hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J)) :
    FiniteDimensional R (P ⧸ J) :=
  irreducible_in_categoryO_finiteDimensional
    (IsCategoryO_quotient _hPO J)
    _hPJ_irr

lemma hom_finrank_eq_countFactorsIso_of_projective
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    (_hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    {J : LieSubmodule R 𝔤 P}
    (_hJ_proper : J ≠ ⊤)
    (_hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)
    (_hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J))
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hMO : IsCategoryO Δ rd M)
    (cs : LieModule.CompositionSeriesOf rd M) :
    Module.finrank R (P →ₗ⁅R, 𝔤⁆ M) = cs.countFactorsIso (P ⧸ J) := by


  rw [hom_finrank_additive_over_composition_series _hPO _hPproj cs]

  unfold LieModule.CompositionSeriesOf.countFactorsIso
  rw [Finset.card_filter]

  apply Finset.sum_congr rfl
  intro i _

  haveI : IsCategoryO Δ rd
      (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl) :=
    compositionFactor_isCategoryO _hMO cs i
  haveI : FiniteDimensional R
      (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl) :=
    compositionFactor_finiteDimensional _hMO cs i

  haveI : FiniteDimensional R (P ⧸ J) :=
    quotient_by_radical_finiteDimensional _hPO _hPJ_irr

  have hkd := projective_hom_simple_kronecker_delta _hJ_proper _hJ_max
    (cs.quotients_irreducible i)

  split_ifs with h
  ·
    exact hkd.1 ⟨h.some.symm⟩
  ·
    exact hkd.2 (fun ⟨iso⟩ => h ⟨iso.symm⟩)

theorem multiplicity_eq_hom_dim
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}

    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)

    {J : LieSubmodule R 𝔤 P}
    (hJ_proper : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)

    (hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J))

    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hMO : IsCategoryO Δ rd M) :

    compositionMultiplicityOfModule M hMO (P ⧸ J) hPJ_irr =
      Module.finrank R (P →ₗ⁅R, 𝔤⁆ M) := by


  unfold compositionMultiplicityOfModule


  exact (hom_finrank_eq_countFactorsIso_of_projective hPO hPproj hindec hJ_proper hJ_max hPJ_irr
    hMO (Classical.choice (categoryO_has_composition_series hMO))).symm

theorem proposition_16_2
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}

    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hindec : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :

    (∃ (J : LieSubmodule R 𝔤 P), J ≠ ⊤ ∧
      (∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J) ∧
      LieModule.IsIrreducible R 𝔤 (P ⧸ J) ∧

      (∀ {L : Type*} [AddCommGroup L] [Module R L]
        [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
        (_hL_simple : LieModule.IsIrreducible R 𝔤 L)
        [FiniteDimensional R (P ⧸ J)],
        (Nonempty (L ≃ₗ⁅R, 𝔤⁆ (P ⧸ J)) → Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) = 1) ∧
        (¬ Nonempty (L ≃ₗ⁅R, 𝔤⁆ (P ⧸ J)) → Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) = 0))) ∧

    (∃ (J : LieSubmodule R 𝔤 P)
      (hJ_proper : J ≠ ⊤)
      (hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)
      (hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J)),
      ∀ {M : Type*} [AddCommGroup M] [Module R M]
        [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
        (hMO : IsCategoryO Δ rd M),
        compositionMultiplicityOfModule M hMO (P ⧸ J) hPJ_irr =
          Module.finrank R (P →ₗ⁅R, 𝔤⁆ M)) := by

  obtain ⟨J, hJ_proper, hJ_max, hPJ_irr⟩ :=
    projective_cover_unique_simple_quotient hPO hPproj hindec
  constructor

  · exact ⟨J, hJ_proper, hJ_max, hPJ_irr, fun {L} _ _ _ _ hL _ =>
      projective_hom_simple_kronecker_delta hJ_proper hJ_max hL⟩

  · exact ⟨J, hJ_proper, hJ_max, hPJ_irr, fun {M} _ _ _ _ hMO =>
      multiplicity_eq_hom_dim hPO hPproj hindec hJ_proper hJ_max hPJ_irr hMO⟩

end
