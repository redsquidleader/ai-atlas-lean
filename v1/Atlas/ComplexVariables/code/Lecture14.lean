/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.Prod
import Atlas.ComplexVariables.code.Lecture13
import Atlas.ComplexVariables.code.CauchyTransformDiff

open Complex MeasureTheory Metric Set Filter Topology

noncomputable section

def residue (f : ℂ → ℂ) (a : ℂ) (R : ℝ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(a, R), f z)

theorem residue_eq_of_differentiableOn_annulus {a : ℂ} {r R : ℝ}
    (hr : 0 < r) (hle : r ≤ R) {f : ℂ → ℂ} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall a R \ ball a r))
    (hd : ∀ z ∈ (ball a R \ closedBall a r) \ s, DifferentiableAt ℂ f z) :
    residue f a R = residue f a r := by
  unfold residue
  congr 1
  exact circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hle hs hc hd

theorem residue_eq_of_differentiableOn_annulus' {a : ℂ} {r R : ℝ}
    (hr : 0 < r) (hle : r ≤ R) {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall a R \ ball a r))
    (hd : ∀ z ∈ ball a R \ closedBall a r, DifferentiableAt ℂ f z) :
    residue f a R = residue f a r :=
  residue_eq_of_differentiableOn_annulus hr hle (s := ∅) countable_empty hc
    (fun z hz => hd z hz.1)

lemma circleIntegral.integral_neg {f : ℂ → ℂ} {c : ℂ} {R : ℝ} :
    (∮ z in C(c, R), -f z) = -(∮ z in C(c, R), f z) := by
  simp only [circleIntegral, smul_neg, intervalIntegral.integral_neg]

set_option maxHeartbeats 3200000 in
theorem principal_part_integral_eq
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {a₀ : ℂ} {r₀ : ℝ}
    {f : ℂ → ℂ}
    (_ha₀ : a₀ ∈ ball c R)
    (hr₀ : 0 < r₀)
    (hrd₀ : closedBall a₀ r₀ ⊆ ball c R)
    (hf_cont : ContinuousOn f (sphere a₀ r₀)) :
    ∮ z in C(c, R), ((2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (w - z)⁻¹ * f w) =
      -∮ w in C(a₀, r₀), f w := by

  have hconv : ∀ z, (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (w - z)⁻¹ * f w =
      -((2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (z - w)⁻¹ * f w) := by
    intro z
    have : (fun w => (w - z)⁻¹ * f w) = (fun w => -((z - w)⁻¹ * f w)) := by
      ext w; rw [show w - z = -(z - w) from by ring, inv_neg, neg_mul]
    rw [this, circleIntegral.integral_neg, mul_neg]
  simp_rw [hconv]
  rw [circleIntegral.integral_neg]
  congr 1

  have hsph_ball : ∀ w ∈ sphere a₀ r₀, w ∈ ball c R :=
    fun w hw => hrd₀ (sphere_subset_closedBall hw)
  have hne : ∀ w ∈ sphere a₀ r₀, ∀ z ∈ sphere c R, z ≠ w := by
    intro w hw z hz hzw; rw [hzw] at hz
    have := hsph_ball w hw; rw [mem_ball] at this; rw [mem_sphere] at hz; linarith

  simp_rw [show ∀ z, (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a₀, r₀), (z - w)⁻¹ * f w =
      (2 * ↑Real.pi * I)⁻¹ • (∮ w in C(a₀, r₀), (z - w)⁻¹ * f w) from
    fun z => (smul_eq_mul _ _).symm]
  rw [circleIntegral.integral_smul, smul_eq_mul]

  suffices h_swap :
    ∮ z in C(c, R), ∮ w in C(a₀, r₀), (z - w)⁻¹ * f w =
    ∮ w in C(a₀, r₀), ∮ z in C(c, R), (z - w)⁻¹ * f w by
    rw [h_swap]

    simp_rw [show ∀ z w : ℂ, (z - w)⁻¹ * f w = f w * (z - w)⁻¹ from fun z w => mul_comm _ _]
    simp_rw [show ∀ w : ℂ, (fun z => f w * (z - w)⁻¹) = (fun z => f w • (z - w)⁻¹) from
      fun w => by ext z; rw [smul_eq_mul]]
    simp_rw [circleIntegral.integral_smul, smul_eq_mul]
    rw [circleIntegral.integral_congr hr₀.le (fun w hw => by
      rw [circleIntegral.integral_sub_inv_of_mem_ball (hsph_ball w hw)])]

    simp_rw [show ∀ w : ℂ, f w * (2 * ↑Real.pi * I) = (2 * ↑Real.pi * I) • f w from
      fun w => by rw [mul_comm, smul_eq_mul]]
    rw [circleIntegral.integral_smul, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

  simp only [circleIntegral]
  simp_rw [← intervalIntegral.integral_smul]
  simp_rw [show ∀ (x y z : ℂ), x • (y • z) = y • (x • z) from fun x y z => by
    simp only [smul_eq_mul]; ring]
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simp_rw [intervalIntegral.integral_of_le hle]
  apply integral_integral_swap

  rw [Measure.prod_restrict]
  apply IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [deriv_circleMap, smul_eq_mul]
  have hf_comp : ContinuousOn (f ∘ circleMap a₀ r₀) (Icc 0 (2 * Real.pi)) := by
    apply hf_cont.comp (continuous_circleMap a₀ r₀).continuousOn
    intro t _; exact circleMap_mem_sphere a₀ hr₀.le t
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact ((continuous_circleMap 0 R).continuousOn.comp continuousOn_fst (mapsTo_univ _ _))
    · exact continuousOn_const
  · apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact ((continuous_circleMap 0 r₀).continuousOn.comp continuousOn_snd (mapsTo_univ _ _))
      · exact continuousOn_const
    · apply ContinuousOn.mul
      · apply ContinuousOn.inv₀
        · exact ((continuous_circleMap c R).continuousOn.comp continuousOn_fst
            (mapsTo_univ _ _)).sub
            ((continuous_circleMap a₀ r₀).continuousOn.comp continuousOn_snd (mapsTo_univ _ _))
        · intro ⟨s, t⟩ ⟨hs, ht⟩
          simp only at hs ht
          exact sub_ne_zero.mpr (hne (circleMap a₀ r₀ t) (circleMap_mem_sphere a₀ hr₀.le t)
            (circleMap c R s) (circleMap_mem_sphere c hR.le s))
      · exact hf_comp.comp continuousOn_snd (fun ⟨_, t⟩ ⟨_, ht⟩ => ht)

open Classical in
theorem diffContOnCl_piecewise_cauchy_extension
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {a : Fin n → ℂ} {r : Fin n → ℝ}
    {f : ℂ → ℂ}
    (hr : ∀ j, 0 < r j)
    (hrd : ∀ j, closedBall (a j) (r j) ⊆ ball c R)
    (h_disj : ∀ i j : Fin n, i ≠ j →
       Disjoint (closedBall (a i) (r i)) (closedBall (a j) (r j)))
    (hcont : ContinuousOn f (closedBall c R \ (⋃ j, ball (a j) (r j))))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j, closedBall (a j) (r j)), DifferentiableAt ℂ f z) :
    let P : Fin n → ℂ → ℂ := fun j z =>
      (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a j, r j), (w - z)⁻¹ * f w
    DiffContOnCl ℂ (fun z => if ∃ j, z ∈ ball (a j) (r j) then ∑ k, P k z
      else f z + ∑ k, P k z) (ball c R) := by sorry

theorem circleIntegral_eq_nonconcentric_of_disjoint_balls
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {a : Fin n → ℂ} {r : Fin n → ℝ}
    {f : ℂ → ℂ}
    (hr : ∀ j, 0 < r j)
    (hrd : ∀ j, closedBall (a j) (r j) ⊆ ball c R)
    (h_disj : ∀ i j : Fin n, i ≠ j →
       Disjoint (closedBall (a i) (r i)) (closedBall (a j) (r j)))
    (hcont : ContinuousOn f (closedBall c R \ (⋃ j, ball (a j) (r j))))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j, closedBall (a j) (r j)), DifferentiableAt ℂ f z) :
    ∮ z in C(c, R), f z = ∑ j : Fin n, ∮ z in C(a j, r j), f z := by
  classical
  have ha_mem : ∀ j, a j ∈ ball c R := fun j =>
    hrd j (mem_closedBall_self (hr j).le)
  let P : Fin n → ℂ → ℂ := fun j z =>
    (2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a j, r j), (w - z)⁻¹ * f w
  have hf_sph : ∀ j, ContinuousOn f (sphere (a j) (r j)) := fun j => by
    apply hcont.mono; intro z hz
    exact ⟨ball_subset_closedBall (hrd j (sphere_subset_closedBall hz)),
      fun hmem => by
        obtain ⟨k, hk⟩ := mem_iUnion.mp hmem
        by_cases hjk : j = k
        · subst hjk; rw [mem_sphere] at hz; rw [mem_ball] at hk; linarith
        · exact Set.disjoint_left.mp (h_disj j k hjk)
            (sphere_subset_closedBall hz) (ball_subset_closedBall hk)⟩
  have hPj_big : ∀ j, ∮ z in C(c, R), P j z = -(∮ w in C(a j, r j), f w) := fun j =>
    principal_part_integral_eq hR (ha_mem j) (hr j) (hrd j) (hf_sph j)
  have hf_ci : CircleIntegrable f c R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact hcont.mono (fun z hz => ⟨sphere_subset_closedBall hz,
      fun hmem => by
        obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
        have := hrd j (ball_subset_closedBall hj)
        rw [mem_sphere] at hz; rw [mem_ball] at this; linarith⟩)
  have hP_diff : ∀ j z, z ∉ sphere (a j) (r j) →
      DifferentiableAt ℂ (P j) z := fun j z hne => by
    have hci : CircleIntegrable f (a j) (r j) :=
      ContinuousOn.circleIntegrable (hr j).le (hf_sph j)
    have heq : (fun z => P j z) =
        (fun z => -((2 * ↑Real.pi * I)⁻¹ * ∮ w in C(a j, r j), (z - w)⁻¹ * f w)) := by
      ext z'; have : (fun w => (w - z')⁻¹ * f w) = (fun w => -((z' - w)⁻¹ * f w)) := by
        ext w; rw [show w - z' = -(z' - w) from by ring, inv_neg, neg_mul]
      simp only [P, this, circleIntegral.integral_neg, mul_neg]
    show DifferentiableAt ℂ (fun z => P j z) z
    rw [heq]
    exact (differentiableAt_cauchy_transform (hr j) hci hne).const_mul _ |>.neg
  have hP_ci : ∀ j, CircleIntegrable (P j) c R := fun j => by
    apply ContinuousOn.circleIntegrable hR.le; intro z hz
    have hne : z ∉ sphere (a j) (r j) := fun hmem => by
      have := hrd j (sphere_subset_closedBall hmem)
      rw [mem_sphere] at hz; rw [mem_ball] at this; linarith
    exact (hP_diff j z hne).continuousAt.continuousWithinAt
  have hsum_ci : CircleIntegrable (fun z => ∑ j, P j z) c R := by
    have h := CircleIntegrable.sum (s := Finset.univ) (f := P) (fun i _ => hP_ci i)
    convert h using 1
    ext z
    simp
  have hlin : ∮ z in C(c, R), (f z + ∑ j, P j z) =
      (∮ z in C(c, R), f z) + ∑ j, ∮ z in C(c, R), P j z := by
    rw [circleIntegral.integral_add hf_ci hsum_ci]; congr 1
    exact circleIntegral.integral_fun_sum (fun i _ => hP_ci i)
  have hsum_eq : ∑ j : Fin n, ∮ z in C(c, R), P j z =
      -(∑ j : Fin n, ∮ z in C(a j, r j), f z) := by
    simp_rw [hPj_big, Finset.sum_neg_distrib]
  suffices key : ∮ z in C(c, R), (f z + ∑ j, P j z) = 0 by
    have h1 : 0 = (∮ z in C(c, R), f z) + ∑ j, ∮ z in C(c, R), P j z := by
      rw [← hlin, key]
    rw [hsum_eq] at h1
    linear_combination -h1

  let G : ℂ → ℂ := fun z =>
    if ∃ j, z ∈ ball (a j) (r j) then ∑ k, P k z
    else f z + ∑ k, P k z
  have hG_sph : ∀ z ∈ sphere c R, G z = f z + ∑ k, P k z := fun z hz => by
    simp only [G]; rw [if_neg]; push Not; intro j hj
    have := hrd j (ball_subset_closedBall hj)
    rw [mem_sphere] at hz; rw [mem_ball] at this; linarith
  rw [show (∮ z in C(c, R), (f z + ∑ j, P j z)) = ∮ z in C(c, R), G z from
    circleIntegral.integral_congr hR.le (fun z hz => (hG_sph z hz).symm)]
  exact DiffContOnCl.circleIntegral_eq_zero hR.le
    (diffContOnCl_piecewise_cauchy_extension hR hr hrd h_disj hcont hdiff)

theorem circleIntegral_eq_sum_of_singularities_bridge
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {a : Fin (n + 1) → ℂ} {r : Fin (n + 1) → ℝ}
    {f : ℂ → ℂ}
    (_hinj : Function.Injective a)
    (_ha : ∀ j, a j ∈ ball c R)
    (hr : ∀ j, 0 < r j)
    (hrd : ∀ j, closedBall (a j) (r j) ⊆ ball c R)
    (h_disj : ∀ i j : Fin (n + 1), i ≠ j →
       Disjoint (closedBall (a i) (r i)) (closedBall (a j) (r j)))
    (hcont : ContinuousOn f (closedBall c R \ (⋃ j, {a j})))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j, {a j}), DifferentiableAt ℂ f z) :
    ∮ z in C(c, R), f z = ∑ j : Fin (n + 1), ∮ z in C(a j, r j), f z := by
  apply circleIntegral_eq_nonconcentric_of_disjoint_balls hR hr hrd h_disj
  · exact hcont.mono (diff_subset_diff_right
      (Set.iUnion_mono (fun j => Set.singleton_subset_iff.mpr (mem_ball_self (hr j)))))
  · intro z ⟨hzball, hznot⟩
    exact hdiff z ⟨hzball, fun hmem => hznot (Set.iUnion_mono
      (fun j => Set.singleton_subset_iff.mpr (mem_closedBall_self (hr j).le)) hmem)⟩

theorem circleIntegral_eq_sum_of_singularities
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {a : Fin n → ℂ} {r : Fin n → ℝ}
    {f : ℂ → ℂ}
    (hinj : Function.Injective a)
    (ha : ∀ j, a j ∈ ball c R)
    (hr : ∀ j, 0 < r j)
    (hrd : ∀ j, closedBall (a j) (r j) ⊆ ball c R)
    (h_disj : ∀ i j : Fin n, i ≠ j →
       Disjoint (closedBall (a i) (r i)) (closedBall (a j) (r j)))
    (hcont : ContinuousOn f (closedBall c R \ (⋃ j, {a j})))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j, {a j}), DifferentiableAt ℂ f z) :
    ∮ z in C(c, R), f z = ∑ j : Fin n, ∮ z in C(a j, r j), f z := by
  match n with
  | 0 =>

    simp only [Finset.univ_eq_empty, Finset.sum_empty, iUnion_of_empty, diff_empty] at *
    apply DiffContOnCl.circleIntegral_eq_zero hR.le
    refine ⟨fun z hz => (hdiff z hz).differentiableWithinAt, ?_⟩
    rwa [closure_ball c (ne_of_gt hR)]
  | n + 1 =>

    exact circleIntegral_eq_sum_of_singularities_bridge hR hinj ha hr hrd h_disj hcont hdiff

theorem residue_theorem_with_disj {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {a : Fin n → ℂ} {f : ℂ → ℂ}
    (ha : ∀ j, a j ∈ ball c R)
    (hinj : Function.Injective a)
    (hcont : ContinuousOn f (closedBall c R \ (⋃ j, {a j})))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j, {a j}), DifferentiableAt ℂ f z)
    {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    (hrd : ∀ j, closedBall (a j) (r j) ⊆ ball c R)
    (h_disj : ∀ i j : Fin n, i ≠ j →
       Disjoint (closedBall (a i) (r i)) (closedBall (a j) (r j))) :
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), f z) =
    ∑ j : Fin n, residue f (a j) (r j) := by
  have hdeform := circleIntegral_eq_sum_of_singularities hR hinj ha hr hrd h_disj hcont hdiff
  unfold residue
  rw [hdeform]
  exact Finset.mul_sum Finset.univ _ _

theorem residue_theorem_aux {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {a : Fin n → ℂ} {f : ℂ → ℂ}
    (ha : ∀ j, a j ∈ ball c R)
    (hinj : Function.Injective a)
    (hcont : ContinuousOn f (closedBall c R \ (⋃ j, {a j})))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j, {a j}), DifferentiableAt ℂ f z)
    {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    (hrd : ∀ j, closedBall (a j) (r j) ⊆ ball c R)
    (h_sep : ∀ i j : Fin n, i ≠ j → a j ∉ closedBall (a i) (r i)) :
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), f z) =
    ∑ j : Fin n, residue f (a j) (r j) := by

  rcases n with _ | n
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, iUnion_of_empty, diff_empty] at *
    have hintf : ∮ z in C(c, R), f z = 0 := by
      apply DiffContOnCl.circleIntegral_eq_zero hR.le
      refine ⟨fun z hz => (hdiff z hz).differentiableWithinAt, ?_⟩
      rwa [closure_ball c (ne_of_gt hR)]
    rw [hintf, mul_zero]


  rcases n.eq_zero_or_pos with rfl | hn
  ·
    exact residue_theorem_with_disj hR ha hinj hcont hdiff hr hrd
      (fun i j hij => absurd (Fin.eq_zero i ▸ Fin.eq_zero j ▸ rfl) hij)

  set S : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2) with S_def
  have hS_ne : S.Nonempty := by
    have h01 : (0 : Fin (n + 1)) ≠ (1 : Fin (n + 1)) := by
      intro h; simp [Fin.ext_iff] at h; omega
    exact ⟨(0, 1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h01⟩⟩
  set d : ℝ := S.inf' hS_ne (fun p => dist (a p.1) (a p.2)) with d_def
  have hd_pos : 0 < d := by
    rw [Finset.lt_inf'_iff]
    intro p hp
    simp only [S_def, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact dist_pos.mpr (fun h => hp (hinj h))
  have hd_le : ∀ i j : Fin (n + 1), i ≠ j → d ≤ dist (a i) (a j) := by
    intro i j hij
    have hmem : (i, j) ∈ S := by
      simp only [S_def, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    exact Finset.inf'_le _ hmem

  set r' : Fin (n + 1) → ℝ := fun j => min (r j) (d / 3) with r'_def
  have hr' : ∀ j, 0 < r' j := fun j => lt_min (hr j) (by linarith)
  have hr'_le : ∀ j, r' j ≤ r j := fun j => min_le_left _ _
  have hr'_le_d3 : ∀ j, r' j ≤ d / 3 := fun j => min_le_right _ _
  have hrd' : ∀ j, closedBall (a j) (r' j) ⊆ ball c R := fun j =>
    (closedBall_subset_closedBall (hr'_le j)).trans (hrd j)

  have h_disj' : ∀ i j : Fin (n + 1), i ≠ j →
      Disjoint (closedBall (a i) (r' i)) (closedBall (a j) (r' j)) := by
    intro i j hij
    simp only [Set.disjoint_left, mem_closedBall]
    intro z h1 h2
    have : d ≤ dist (a i) (a j) := hd_le i j hij
    linarith [dist_triangle_left (a i) (a j) z, hr'_le_d3 i, hr'_le_d3 j]

  have hres' := residue_theorem_with_disj hR ha hinj hcont hdiff hr' hrd' h_disj'

  suffices heq : ∀ j, residue f (a j) (r j) = residue f (a j) (r' j) by
    rw [hres']; congr 1; ext j; exact (heq j).symm
  intro j
  apply residue_eq_of_differentiableOn_annulus' (hr' j) (hr'_le j)

  · apply hcont.mono
    intro z hz
    constructor
    · exact ball_subset_closedBall (hrd j hz.1)
    · rw [mem_iUnion]; push Not; intro k
      rw [mem_singleton_iff]
      intro hzk; subst hzk
      by_cases hjk : j = k
      · subst hjk; exact hz.2 (mem_ball_self (hr' j))
      · exact absurd hz.1 (h_sep j k hjk)

  · intro z hz
    apply hdiff z
    constructor
    · exact hrd j (ball_subset_closedBall hz.1)
    · rw [mem_iUnion]; push Not; intro k
      rw [mem_singleton_iff]
      intro hzk; subst hzk
      by_cases hjk : j = k
      · subst hjk; exact hz.2 (mem_closedBall_self (hr' j).le)
      · exact absurd (mem_closedBall.mpr (mem_ball.mp hz.1).le) (h_sep j k hjk)

theorem residue_theorem {c : ℂ} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {a : Fin n → ℂ} {f : ℂ → ℂ}
    (ha : ∀ j, a j ∈ ball c R)
    (hinj : Function.Injective a)
    (hcont : ContinuousOn f (closedBall c R \ (⋃ j, {a j})))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j, {a j}), DifferentiableAt ℂ f z)
    {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    (hrd : ∀ j, closedBall (a j) (r j) ⊆ ball c R)
    (h_sep : ∀ i j : Fin n, i ≠ j → a j ∉ closedBall (a i) (r i)) :
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), f z) =
    ∑ j : Fin n, residue f (a j) (r j) :=
  residue_theorem_aux hR ha hinj hcont hdiff hr hrd h_sep

open Finset in

abbrev singPts {nz np : ℕ} (zeros : Fin nz → ℂ) (poles : Fin np → ℂ) : Fin (nz + np) → ℂ :=
  Fin.addCases zeros poles

abbrev singRads {nz np : ℕ} (rz : Fin nz → ℝ) (rp : Fin np → ℝ) : Fin (nz + np) → ℝ :=
  Fin.addCases rz rp

lemma logDeriv_sub_zpow (b : ℂ) (n : ℤ) (z : ℂ) (hz : z ≠ b) :
    logDeriv (fun x => (x - b) ^ n) z = n / (z - b) := by
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr hz
  have : (fun x => (x - b) ^ n) = (fun x => x ^ n) ∘ (fun x => x - b) := by ext; simp
  rw [this, logDeriv_comp]
  · simp [logDeriv_zpow]
  · exact differentiableAt_zpow.mpr (Or.inl hzb)
  · exact differentiableAt_id.sub (differentiableAt_const b)

theorem continuousOn_deriv_of_differentiableAt_closedBall
    {b : ℂ} {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ}
    (hg_hol : ∀ z ∈ closedBall b ε, DifferentiableAt ℂ g z) :
    ContinuousOn (deriv g) (closedBall b ε) := by sorry

lemma circleIntegral_logDeriv_eq_zero {b : ℂ} {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ}
    (hg_hol : ∀ z ∈ closedBall b ε, DifferentiableAt ℂ g z)
    (hg_cont : ContinuousOn g (closedBall b ε))
    (hg_ne : ∀ z ∈ closedBall b ε, g z ≠ 0) :
    ∮ z in C(b, ε), logDeriv g z = 0 := by
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le (s := ∅) countable_empty
  ·
    unfold logDeriv
    apply ContinuousOn.div
    · exact continuousOn_deriv_of_differentiableAt_closedBall hε hg_hol
    · exact hg_cont
    · exact fun z hz => hg_ne z hz
  ·
    intro z ⟨hz, _⟩
    have hzb := ball_subset_closedBall hz
    have hg_diffOn : DifferentiableOn ℂ g (ball b ε) :=
      fun w hw => (hg_hol w (ball_subset_closedBall hw)).differentiableWithinAt
    unfold logDeriv
    apply DifferentiableAt.div
    · exact ((hg_diffOn.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz))
    · exact hg_hol z hzb
    · exact hg_ne z hzb

lemma logDeriv_zero_decomposition {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    {f : ℂ → ℂ} {n : ℕ} {g : ℂ → ℂ}
    (hg_hol : ∀ z ∈ closedBall a ε, DifferentiableAt ℂ g z)
    (hg_ne : ∀ z ∈ sphere a ε, g z ≠ 0)
    (hf_nhds : ∀ z ∈ sphere a ε, ∀ᶠ w in 𝓝 z, f w = (w - a) ^ n * g w) :
    EqOn (logDeriv f) (fun z => (n : ℂ) / (z - a) + logDeriv g z) (sphere a ε) := by
  intro z hz
  have hza : z ≠ a := ne_of_mem_sphere hz hε.ne'
  have hfe : f =ᶠ[𝓝 z] fun w => (w - a) ^ n * g w := hf_nhds z hz
  have hlf : logDeriv f z = logDeriv (fun w => (w - a) ^ n * g w) z := by
    unfold logDeriv; simp only [Pi.div_apply]; rw [hfe.deriv_eq, hfe.eq_of_nhds]
  rw [hlf]
  have hg_diff : DifferentiableAt ℂ g z := hg_hol z (sphere_subset_closedBall hz)
  have hg_nez : g z ≠ 0 := hg_ne z hz
  have hpow_diff : DifferentiableAt ℂ (fun w => (w - a) ^ n) z :=
    (differentiableAt_id.sub (differentiableAt_const a)).pow n
  have hpow_ne : (z - a) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hza)
  have key := logDeriv_mul (f := fun w => (w - a) ^ n) (g := g) z hpow_ne hg_nez hpow_diff hg_diff
  rw [key]
  congr 1
  have heq : (fun w : ℂ => (w - a) ^ n) = (fun w => (w - a) ^ (n : ℤ)) := by
    ext w; simp [zpow_natCast]
  rw [heq, logDeriv_sub_zpow a (n : ℤ) z hza]; simp

theorem residue_logDeriv_at_zero {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    {f : ℂ → ℂ} {h : ℕ} (_hh : 0 < h) {g : ℂ → ℂ}
    (hg_ne : ∀ z ∈ closedBall a ε, g z ≠ 0)
    (hg_hol : ∀ z ∈ closedBall a ε, DifferentiableAt ℂ g z)
    (hg_cont : ContinuousOn g (closedBall a ε))
    (_hf_eq : ∀ z ∈ closedBall a ε \ {a}, f z = (z - a) ^ h * g z)
    (hf_nhds : ∀ z ∈ sphere a ε, ∀ᶠ w in 𝓝 z, f w = (w - a) ^ h * g w) :
    residue (logDeriv f) a ε = (h : ℂ) := by
  simp only [residue]
  suffices hsuff : ∮ z in C(a, ε), logDeriv f z = (h : ℂ) * (2 * ↑Real.pi * I) by
    rw [hsuff]; field_simp

  rw [circleIntegral.integral_congr hε.le
    (logDeriv_zero_decomposition hε hg_hol (fun z hz => hg_ne z (sphere_subset_closedBall hz)) hf_nhds)]

  have hci1 : CircleIntegrable (fun z => (h : ℂ) / (z - a)) a ε := by
    apply ContinuousOn.circleIntegrable hε.le
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro z hz; exact sub_ne_zero.mpr (ne_of_mem_sphere hz hε.ne')
  have hci2 : CircleIntegrable (fun z => logDeriv g z) a ε := by
    apply ContinuousOn.circleIntegrable hε.le
    show ContinuousOn (fun z => logDeriv g z) (sphere a ε)
    have : ContinuousOn (fun z => deriv g z / g z) (sphere a ε) := by
      apply ContinuousOn.div
      · exact (continuousOn_deriv_of_differentiableAt_closedBall hε hg_hol).mono
          sphere_subset_closedBall
      · exact hg_cont.mono sphere_subset_closedBall
      · exact fun z hz => hg_ne z (sphere_subset_closedBall hz)
    exact this.congr (fun z hz => by simp [logDeriv])
  rw [circleIntegral.integral_add hci1 hci2]

  have hint1 : (∮ z in C(a, ε), (h : ℂ) / (z - a)) = (h : ℂ) * (2 * ↑Real.pi * I) := by
    have : (fun z => (h : ℂ) / (z - a)) = fun z => (h : ℂ) • (z - a)⁻¹ := by
      ext z; simp [smul_eq_mul, div_eq_mul_inv]
    rw [this, circleIntegral.integral_smul,
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hε)]
    simp [smul_eq_mul]

  have hint2 : (∮ z in C(a, ε), logDeriv g z) = 0 :=
    circleIntegral_logDeriv_eq_zero hε hg_hol hg_cont hg_ne
  rw [hint1, hint2, add_zero]

lemma logDeriv_pole_decomposition {b : ℂ} {ε : ℝ} (hε : 0 < ε)
    {f : ℂ → ℂ} {k : ℕ} {g : ℂ → ℂ}
    (hg_hol : ∀ z ∈ closedBall b ε, DifferentiableAt ℂ g z)
    (hg_ne : ∀ z ∈ sphere b ε, g z ≠ 0)
    (hf_eq : ∀ z ∈ sphere b ε, ∀ᶠ w in 𝓝 z, f w = ((w - b) ^ k)⁻¹ * g w) :
    EqOn (logDeriv f) (fun z => -(k : ℂ) / (z - b) + logDeriv g z) (sphere b ε) := by
  intro z hz
  have hzb : z ≠ b := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hfe : f =ᶠ[𝓝 z] fun w => ((w - b) ^ k)⁻¹ * g w := hf_eq z hz

  have hlf : logDeriv f z = logDeriv (fun w => ((w - b) ^ k)⁻¹ * g w) z := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [hfe.deriv_eq, hfe.eq_of_nhds]
  rw [hlf]

  have hg_diff : DifferentiableAt ℂ g z := hg_hol z (sphere_subset_closedBall hz)
  have hg_nez : g z ≠ 0 := hg_ne z hz
  have hpow_diff : DifferentiableAt ℂ (fun w => ((w - b) ^ k)⁻¹) z := by
    apply DifferentiableAt.inv
    · exact (differentiableAt_id.sub (differentiableAt_const b)).pow k
    · exact pow_ne_zero k (sub_ne_zero.mpr hzb)
  have hpow_ne : ((z - b) ^ k)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero k (sub_ne_zero.mpr hzb))
  rw [logDeriv_mul z hpow_ne hg_nez hpow_diff hg_diff]

  congr 1
  have heq : (fun w : ℂ => ((w - b) ^ k)⁻¹) = (fun w => (w - b) ^ (-(k : ℤ))) := by
    ext w; simp [zpow_neg, zpow_natCast]
  rw [heq, logDeriv_sub_zpow b (-(k : ℤ)) z hzb]
  push_cast; ring

theorem residue_logDeriv_at_pole {b : ℂ} {ε : ℝ} (hε : 0 < ε)
    {f : ℂ → ℂ} {k : ℕ} (_hk : 0 < k) {g : ℂ → ℂ}
    (hg_ne : ∀ z ∈ closedBall b ε, g z ≠ 0)
    (hg_hol : ∀ z ∈ closedBall b ε, DifferentiableAt ℂ g z)
    (hg_cont : ContinuousOn g (closedBall b ε))
    (_hf_eq : ∀ z ∈ closedBall b ε \ {b}, f z = ((z - b) ^ k)⁻¹ * g z)
    (hf_eq_nhds : ∀ z ∈ sphere b ε, ∀ᶠ w in 𝓝 z, f w = ((w - b) ^ k)⁻¹ * g w) :
    residue (logDeriv f) b ε = -(k : ℂ) := by


  simp only [residue]
  suffices h : ∮ z in C(b, ε), logDeriv f z = -(k : ℂ) * (2 * ↑Real.pi * I) by
    rw [h]; field_simp

  rw [circleIntegral.integral_congr hε.le
    (logDeriv_pole_decomposition hε hg_hol (fun z hz => hg_ne z (sphere_subset_closedBall hz)) hf_eq_nhds)]

  have hci1 : CircleIntegrable (fun z => -(k : ℂ) / (z - b)) b ε := by
    apply ContinuousOn.circleIntegrable hε.le
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro z hz; exact sub_ne_zero.mpr (ne_of_mem_sphere hz hε.ne')
  have hci2 : CircleIntegrable (fun z => logDeriv g z) b ε := by
    apply ContinuousOn.circleIntegrable hε.le
    show ContinuousOn (fun z => logDeriv g z) (sphere b ε)
    have : ContinuousOn (fun z => deriv g z / g z) (sphere b ε) := by
      apply ContinuousOn.div
      · exact (continuousOn_deriv_of_differentiableAt_closedBall hε hg_hol).mono
          sphere_subset_closedBall
      · exact hg_cont.mono sphere_subset_closedBall
      · exact fun z hz => hg_ne z (sphere_subset_closedBall hz)
    exact this.congr (fun z hz => by simp [logDeriv])
  rw [circleIntegral.integral_add hci1 hci2]

  have hint1 : (∮ z in C(b, ε), -(k : ℂ) / (z - b)) = -(k : ℂ) * (2 * ↑Real.pi * I) := by
    have : (fun z => -(k : ℂ) / (z - b)) = fun z => -(k : ℂ) • (z - b)⁻¹ := by
      ext z; simp [smul_eq_mul, div_eq_mul_inv]
    rw [this, circleIntegral.integral_smul,
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hε)]
    simp [smul_eq_mul]

  have hint2 : (∮ z in C(b, ε), logDeriv g z) = 0 :=
    circleIntegral_logDeriv_eq_zero hε hg_hol hg_cont hg_ne
  rw [hint1, hint2, add_zero]

theorem argument_principle {c : ℂ} {R : ℝ} (hR : 0 < R)
    {nz np : ℕ}
    {zeros : Fin nz → ℂ} {poles : Fin np → ℂ}
    {multZ : Fin nz → ℕ} {multP : Fin np → ℕ}
    {rz : Fin nz → ℝ} {rp : Fin np → ℝ}
    {f : ℂ → ℂ}
    {gz : Fin nz → ℂ → ℂ} {gp : Fin np → ℂ → ℂ}

    (hzeros_in : ∀ j, zeros j ∈ ball c R)
    (hpoles_in : ∀ j, poles j ∈ ball c R)

    (hrz : ∀ j, 0 < rz j) (hrp : ∀ j, 0 < rp j)

    (hmz_pos : ∀ j, 0 < multZ j) (hmp_pos : ∀ j, 0 < multP j)

    (hrz_sub : ∀ j, closedBall (zeros j) (rz j) ⊆ ball c R)
    (hrp_sub : ∀ j, closedBall (poles j) (rp j) ⊆ ball c R)

    (hinj_pts : Function.Injective (singPts zeros poles))

    (hcont : ContinuousOn (logDeriv f)
      (closedBall c R \ (⋃ j : Fin (nz + np), {singPts zeros poles j})))

    (hdiff : ∀ z ∈ ball c R \ (⋃ j : Fin (nz + np), {singPts zeros poles j}),
      DifferentiableAt ℂ (logDeriv f) z)

    (hgz_ne : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j), gz j z ≠ 0)
    (hgz_hol : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j), DifferentiableAt ℂ (gz j) z)
    (hgz_cont : ∀ j, ContinuousOn (gz j) (closedBall (zeros j) (rz j)))
    (hf_zero : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j) \ {zeros j},
      f z = (z - zeros j) ^ multZ j * gz j z)
    (hf_zero_nhds : ∀ j, ∀ z ∈ sphere (zeros j) (rz j),
      ∀ᶠ w in 𝓝 z, f w = (w - zeros j) ^ multZ j * gz j w)

    (hgp_ne : ∀ j, ∀ z ∈ closedBall (poles j) (rp j), gp j z ≠ 0)
    (hgp_hol : ∀ j, ∀ z ∈ closedBall (poles j) (rp j), DifferentiableAt ℂ (gp j) z)
    (hgp_cont : ∀ j, ContinuousOn (gp j) (closedBall (poles j) (rp j)))
    (hf_pole : ∀ j, ∀ z ∈ closedBall (poles j) (rp j) \ {poles j},
      f z = ((z - poles j) ^ multP j)⁻¹ * gp j z)
    (hf_pole_nhds : ∀ j, ∀ z ∈ sphere (poles j) (rp j),
      ∀ᶠ w in 𝓝 z, f w = ((w - poles j) ^ multP j)⁻¹ * gp j w) :

    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) =
    ↑((∑ j : Fin nz, (multZ j : ℤ)) - (∑ j : Fin np, (multP j : ℤ))) := by


  set pts := singPts zeros poles with pts_def
  set rads := singRads rz rp with rads_def

  have ha : ∀ j, pts j ∈ ball c R := by
    intro j; simp only [pts_def, singPts]
    exact Fin.addCases (fun i => by simp [Fin.addCases_left]; exact hzeros_in i)
      (fun i => by simp [Fin.addCases_right]; exact hpoles_in i) j
  have hr : ∀ j, 0 < rads j := by
    intro j; simp only [rads_def, singRads]
    exact Fin.addCases (fun i => by simp [Fin.addCases_left]; exact hrz i)
      (fun i => by simp [Fin.addCases_right]; exact hrp i) j
  have hrd : ∀ j, closedBall (pts j) (rads j) ⊆ ball c R := by
    intro j; simp only [pts_def, rads_def, singPts, singRads]
    exact Fin.addCases (fun i => by simp [Fin.addCases_left]; exact hrz_sub i)
      (fun i => by simp [Fin.addCases_right]; exact hrp_sub i) j

  have hdist_pos : ∀ i j : Fin (nz + np), i ≠ j → 0 < dist (pts i) (pts j) := by
    intro i j hij
    exact dist_pos.mpr (hinj_pts.ne hij)


  let N := nz + np

  by_cases hN : N = 0
  ·
    have hnz : nz = 0 := Nat.eq_zero_of_add_eq_zero_right hN
    have hnp : np = 0 := Nat.eq_zero_of_add_eq_zero_left hN
    subst hnz; subst hnp
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_self, Int.cast_zero]
    suffices h : ∮ z in C(c, R), logDeriv f z = 0 by rw [h, mul_zero]
    have : (⋃ j : Fin (0 + 0), {pts j}) = ∅ := by simp [iUnion_of_empty]
    rw [this, diff_empty] at hcont hdiff
    apply DiffContOnCl.circleIntegral_eq_zero hR.le
    refine ⟨fun z hz => (hdiff z hz).differentiableWithinAt, ?_⟩
    rwa [closure_ball c (ne_of_gt hR)]
  ·
    have hN_pos : 0 < N := Nat.pos_of_ne_zero hN

    let rads' : Fin N → ℝ := fun i =>
      Finset.inf' Finset.univ ⟨i, Finset.mem_univ i⟩ fun j =>
        if j = i then rads i
        else min (rads i) (dist (pts i) (pts j) / 3)
    have hrads'_pos : ∀ j, 0 < rads' j := by
      intro j
      rw [Finset.lt_inf'_iff]
      intro k _
      split_ifs with hk
      · exact hr j
      · exact lt_min (hr j) (div_pos (hdist_pos j k (Ne.symm hk)) (by norm_num))
    have hrads'_le : ∀ j, rads' j ≤ rads j := by
      intro j
      exact (Finset.inf'_le _ (Finset.mem_univ j)).trans (by simp)
    have hrads'_le_dist : ∀ i j : Fin N, i ≠ j → rads' i ≤ dist (pts i) (pts j) / 3 := by
      intro i j hij
      apply (Finset.inf'_le _ (Finset.mem_univ j)).trans
      simp only [hij.symm, ↓reduceIte]
      exact min_le_right _ _

    have hrd' : ∀ j, closedBall (pts j) (rads' j) ⊆ ball c R :=
      fun j => (closedBall_subset_closedBall (hrads'_le j)).trans (hrd j)

    have hdisj' : ∀ i j : Fin N, i ≠ j →
        Disjoint (closedBall (pts i) (rads' i)) (closedBall (pts j) (rads' j)) := by
      intro i j hij; rw [Set.disjoint_iff]; intro z ⟨hi, hj⟩
      rw [mem_closedBall] at hi hj
      have htri := dist_triangle_left (pts i) (pts j) z
      have hdi := hrads'_le_dist i j hij
      have hdj := hrads'_le_dist j i hij.symm
      rw [dist_comm (pts j) (pts i)] at hdj
      nlinarith [hdist_pos i j hij]

    have hdeform := circleIntegral_eq_sum_of_singularities hR hinj_pts ha hrads'_pos hrd'
      hdisj' hcont hdiff

    rw [hdeform, Finset.mul_sum, Fin.sum_univ_add]

    simp only [pts_def, Fin.addCases_left, Fin.addCases_right]


    have hrads'_z : ∀ j : Fin nz, 0 < rads' (Fin.castAdd np j) := fun j => hrads'_pos _
    have hrads'_p : ∀ j : Fin np, 0 < rads' (Fin.natAdd nz j) := fun j => hrads'_pos _

    have hrads'_le_rz : ∀ j : Fin nz,
        rads' (Fin.castAdd np j) ≤ rz j := by
      intro j; exact (hrads'_le _).trans (by simp [rads_def, Fin.addCases_left])

    have hrads'_le_rp : ∀ j : Fin np,
        rads' (Fin.natAdd nz j) ≤ rp j := by
      intro j; exact (hrads'_le _).trans (by simp [rads_def, Fin.addCases_right])

    have hgz_ne' : ∀ j, ∀ z ∈ closedBall (zeros j) (rads' (Fin.castAdd np j)), gz j z ≠ 0 :=
      fun j z hz => hgz_ne j z (closedBall_subset_closedBall (hrads'_le_rz j) hz)
    have hgz_hol' : ∀ j, ∀ z ∈ closedBall (zeros j) (rads' (Fin.castAdd np j)),
        DifferentiableAt ℂ (gz j) z :=
      fun j z hz => hgz_hol j z (closedBall_subset_closedBall (hrads'_le_rz j) hz)
    have hgz_cont' : ∀ j, ContinuousOn (gz j) (closedBall (zeros j) (rads' (Fin.castAdd np j))) :=
      fun j => hgz_cont j |>.mono (closedBall_subset_closedBall (hrads'_le_rz j))
    have hf_zero' : ∀ j, ∀ z ∈ closedBall (zeros j) (rads' (Fin.castAdd np j)) \ {zeros j},
        f z = (z - zeros j) ^ multZ j * gz j z := by
      intro j z ⟨hz, hne⟩
      exact hf_zero j z ⟨closedBall_subset_closedBall (hrads'_le_rz j) hz, hne⟩
    have hf_zero_nhds' : ∀ j, ∀ z ∈ sphere (zeros j) (rads' (Fin.castAdd np j)),
        ∀ᶠ w in 𝓝 z, f w = (w - zeros j) ^ multZ j * gz j w := by
      intro j z hz
      have hzd : dist z (zeros j) = rads' (Fin.castAdd np j) := mem_sphere.mp hz
      have hz_ne : z ≠ zeros j := by
        intro heq; rw [heq, dist_self] at hzd; linarith [hrads'_z j]


      by_cases heq : rads' (Fin.castAdd np j) = rz j
      ·
        have hz' : z ∈ sphere (zeros j) (rz j) := by rwa [mem_sphere, hzd]
        exact hf_zero_nhds j z hz'
      ·
        have hlt : rads' (Fin.castAdd np j) < rz j :=
          lt_of_le_of_ne (hrads'_le_rz j) heq
        rw [Metric.eventually_nhds_iff]
        refine ⟨min (rz j - rads' (Fin.castAdd np j)) (rads' (Fin.castAdd np j)),
          lt_min (by linarith) (hrads'_z j), fun w hw => ?_⟩
        apply hf_zero j w
        constructor
        · rw [mem_closedBall]
          have : dist w (zeros j) < rz j :=
            calc dist w (zeros j) ≤ dist w z + dist z (zeros j) := dist_triangle _ _ _
              _ = dist w z + rads' (Fin.castAdd np j) := by rw [hzd]
              _ < min (rz j - rads' (Fin.castAdd np j)) (rads' (Fin.castAdd np j)) +
                    rads' (Fin.castAdd np j) := by linarith
              _ ≤ (rz j - rads' (Fin.castAdd np j)) + rads' (Fin.castAdd np j) := by
                  linarith [min_le_left (rz j - rads' (Fin.castAdd np j)) (rads' (Fin.castAdd np j))]
              _ = rz j := by ring
          linarith
        · rw [Set.mem_singleton_iff]; intro heq'
          rw [heq'] at hw; simp only [dist_comm] at hw; rw [hzd] at hw
          linarith [min_le_right (rz j - rads' (Fin.castAdd np j)) (rads' (Fin.castAdd np j))]

    have hgp_ne' : ∀ j, ∀ z ∈ closedBall (poles j) (rads' (Fin.natAdd nz j)), gp j z ≠ 0 :=
      fun j z hz => hgp_ne j z (closedBall_subset_closedBall (hrads'_le_rp j) hz)
    have hgp_hol' : ∀ j, ∀ z ∈ closedBall (poles j) (rads' (Fin.natAdd nz j)),
        DifferentiableAt ℂ (gp j) z :=
      fun j z hz => hgp_hol j z (closedBall_subset_closedBall (hrads'_le_rp j) hz)
    have hgp_cont' : ∀ j, ContinuousOn (gp j) (closedBall (poles j) (rads' (Fin.natAdd nz j))) :=
      fun j => hgp_cont j |>.mono (closedBall_subset_closedBall (hrads'_le_rp j))
    have hf_pole' : ∀ j, ∀ z ∈ closedBall (poles j) (rads' (Fin.natAdd nz j)) \ {poles j},
        f z = ((z - poles j) ^ multP j)⁻¹ * gp j z := by
      intro j z ⟨hz, hne⟩
      exact hf_pole j z ⟨closedBall_subset_closedBall (hrads'_le_rp j) hz, hne⟩
    have hf_pole_nhds' : ∀ j, ∀ z ∈ sphere (poles j) (rads' (Fin.natAdd nz j)),
        ∀ᶠ w in 𝓝 z, f w = ((w - poles j) ^ multP j)⁻¹ * gp j w := by
      intro j z hz
      have hzd : dist z (poles j) = rads' (Fin.natAdd nz j) := mem_sphere.mp hz
      have hz_ne : z ≠ poles j := by
        intro heq; rw [heq, dist_self] at hzd; linarith [hrads'_p j]
      by_cases heq : rads' (Fin.natAdd nz j) = rp j
      · have hz' : z ∈ sphere (poles j) (rp j) := by rwa [mem_sphere, hzd]
        exact hf_pole_nhds j z hz'
      · have hlt : rads' (Fin.natAdd nz j) < rp j :=
          lt_of_le_of_ne (hrads'_le_rp j) heq
        rw [Metric.eventually_nhds_iff]
        refine ⟨min (rp j - rads' (Fin.natAdd nz j)) (rads' (Fin.natAdd nz j)),
          lt_min (by linarith) (hrads'_p j), fun w hw => ?_⟩
        apply hf_pole j w
        constructor
        · rw [mem_closedBall]
          have : dist w (poles j) < rp j :=
            calc dist w (poles j) ≤ dist w z + dist z (poles j) := dist_triangle _ _ _
              _ = dist w z + rads' (Fin.natAdd nz j) := by rw [hzd]
              _ < min (rp j - rads' (Fin.natAdd nz j)) (rads' (Fin.natAdd nz j)) +
                    rads' (Fin.natAdd nz j) := by linarith
              _ ≤ (rp j - rads' (Fin.natAdd nz j)) + rads' (Fin.natAdd nz j) := by
                  linarith [min_le_left (rp j - rads' (Fin.natAdd nz j)) (rads' (Fin.natAdd nz j))]
              _ = rp j := by ring
          linarith
        · rw [Set.mem_singleton_iff]; intro heq'
          rw [heq'] at hw; simp only [dist_comm] at hw; rw [hzd] at hw
          linarith [min_le_right (rp j - rads' (Fin.natAdd nz j)) (rads' (Fin.natAdd nz j))]

    have hresZ : ∀ j : Fin nz,
        (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(zeros j, rads' (Fin.castAdd np j)),
          logDeriv f z) = (multZ j : ℂ) :=
      fun j => residue_logDeriv_at_zero (hrads'_z j) (hmz_pos j)
        (hgz_ne' j) (hgz_hol' j) (hgz_cont' j) (hf_zero' j) (hf_zero_nhds' j)
    have hresP : ∀ j : Fin np,
        (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(poles j, rads' (Fin.natAdd nz j)),
          logDeriv f z) = -(multP j : ℂ) :=
      fun j => residue_logDeriv_at_pole (hrads'_p j) (hmp_pos j)
        (hgp_ne' j) (hgp_hol' j) (hgp_cont' j) (hf_pole' j) (hf_pole_nhds' j)


    simp_rw [hresZ, hresP]

    push_cast
    rw [Finset.sum_neg_distrib]
    ring

theorem circleIntegral_logDeriv_eq_zero_of_image_in_unit_ball
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ψ : ℂ → ℂ}
    (hψ_diff : ∀ z ∈ sphere c R, DifferentiableAt ℂ ψ z)
    (_hψ_cont : ContinuousOn ψ (sphere c R))
    (hψ_bound : ∀ z ∈ sphere c R, ‖ψ z - 1‖ < 1) :
    ∮ z in C(c, R), logDeriv ψ z = 0 := by

  have hψ_slit : ∀ z ∈ sphere c R, ψ z ∈ slitPlane := fun z hz => by
    have h := hψ_bound z hz
    have : ψ z = 1 + (ψ z - 1) := by ring
    rw [this]; exact mem_slitPlane_of_norm_lt_one h


  exact circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le fun z hz => by
    have heq : deriv (log ∘ ψ) z = logDeriv ψ z :=
      Complex.deriv_log_comp_eq_logDeriv (hψ_diff z hz) (hψ_slit z hz)
    rw [← heq]
    exact ((hψ_diff z hz).clog (hψ_slit z hz)).hasDerivAt.hasDerivWithinAt

theorem rouche_integral_eq {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f g : ℂ → ℂ}

    (hf_diff : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hg_diff : ∀ z ∈ closedBall c R, DifferentiableAt ℂ g z)

    (hbound : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖)


    (hf_int : CircleIntegrable (logDeriv f) c R)
    (hg_int : CircleIntegrable (logDeriv g) c R) :
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv g z) =
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) := by

  congr 1


  have hf_ne : ∀ z ∈ sphere c R, f z ≠ 0 := by
    intro z hz hfz; have := hbound z hz; rw [hfz, norm_zero] at this
    exact not_lt.mpr (norm_nonneg _) this


  have hg_ne : ∀ z ∈ sphere c R, g z ≠ 0 := by
    intro z hz hgz; have := hbound z hz; rw [hgz, sub_zero] at this; exact lt_irrefl _ this

  have hψ_bound : ∀ z ∈ sphere c R, ‖g z / f z - 1‖ < 1 := by
    intro z hz
    have hfz := hf_ne z hz
    rw [div_sub_one hfz, norm_div, div_lt_one (norm_pos_iff.mpr hfz), norm_sub_rev]
    exact hbound z hz

  have hsphere_sub : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  have hgf_diff : ∀ z ∈ sphere c R, DifferentiableAt ℂ (fun z => g z / f z) z :=
    fun z hz => (hg_diff z (hsphere_sub hz)).div (hf_diff z (hsphere_sub hz)) (hf_ne z hz)
  have hgf_cont : ContinuousOn (fun z => g z / f z) (sphere c R) :=
    fun z hz => (hgf_diff z hz).continuousAt.continuousWithinAt

  have h_zero :=
    circleIntegral_logDeriv_eq_zero_of_image_in_unit_ball hR hgf_diff hgf_cont hψ_bound


  have h_eq : EqOn (logDeriv (fun z => g z / f z))
      (fun z => logDeriv g z - logDeriv f z) (sphere c R) :=
    fun z hz => logDeriv_div z (hg_ne z hz) (hf_ne z hz)
      (hg_diff z (hsphere_sub hz)) (hf_diff z (hsphere_sub hz))

  rw [circleIntegral.integral_congr hR.le h_eq] at h_zero
  rw [circleIntegral.integral_sub hg_int hf_int] at h_zero

  exact sub_eq_zero.mp h_zero

lemma argument_principle_no_poles {c : ℂ} {R : ℝ} (hR : 0 < R)
    {nz : ℕ} {zeros : Fin nz → ℂ} {multZ : Fin nz → ℕ}
    {rz : Fin nz → ℝ} {f : ℂ → ℂ} {gz : Fin nz → ℂ → ℂ}
    (hzeros_in : ∀ j, zeros j ∈ ball c R)
    (hrz : ∀ j, 0 < rz j)
    (hmz_pos : ∀ j, 0 < multZ j)
    (hrz_sub : ∀ j, closedBall (zeros j) (rz j) ⊆ ball c R)
    (hdisj : ∀ i j : Fin nz, i ≠ j →
      Disjoint (closedBall (zeros i) (rz i)) (closedBall (zeros j) (rz j)))
    (hcont : ContinuousOn (logDeriv f)
      (closedBall c R \ (⋃ j : Fin nz, {zeros j})))
    (hdiff : ∀ z ∈ ball c R \ (⋃ j : Fin nz, {zeros j}),
      DifferentiableAt ℂ (logDeriv f) z)
    (hgz_ne : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j), gz j z ≠ 0)
    (hgz_hol : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j), DifferentiableAt ℂ (gz j) z)
    (hgz_cont : ∀ j, ContinuousOn (gz j) (closedBall (zeros j) (rz j)))
    (hf_zero : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j) \ {zeros j},
      f z = (z - zeros j) ^ multZ j * gz j z)
    (hf_zero_nhds : ∀ j, ∀ z ∈ sphere (zeros j) (rz j),
      ∀ᶠ w in 𝓝 z, f w = (w - zeros j) ^ multZ j * gz j w) :
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) =
    ↑(∑ j : Fin nz, (multZ j : ℤ)) := by


  have singPts_elim0 : ∀ i : Fin (nz + 0),
      singPts zeros (Fin.elim0 : Fin 0 → ℂ) i = zeros i := by
    intro ⟨i, hi⟩; simp [singPts, Fin.addCases, show i < nz from hi]
  have singRads_elim0 : ∀ i : Fin (nz + 0),
      singRads rz (Fin.elim0 : Fin 0 → ℝ) i = rz i := by
    intro ⟨i, hi⟩; simp [singRads, Fin.addCases, show i < nz from hi]

  have hset_eq : (⋃ j : Fin (nz + 0), {singPts zeros (Fin.elim0 : Fin 0 → ℂ) j}) =
      ⋃ j : Fin nz, {zeros j} := by
    congr 1; ext1 j; simp only [singPts_elim0]

  have key := argument_principle hR
    (zeros := zeros) (poles := (Fin.elim0 : Fin 0 → ℂ))
    (multZ := multZ) (multP := (Fin.elim0 : Fin 0 → ℕ))
    (rz := rz) (rp := (Fin.elim0 : Fin 0 → ℝ))
    (gz := gz) (gp := (Fin.elim0 : Fin 0 → ℂ → ℂ))
    hzeros_in (fun j => Fin.elim0 j) hrz (fun j => Fin.elim0 j)
    hmz_pos (fun j => Fin.elim0 j) hrz_sub (fun j => Fin.elim0 j)
    (by
        intro i j hij; simp only [singPts_elim0] at hij
        by_contra h; exact Set.disjoint_left.mp (hdisj i j h)
          (mem_closedBall_self (le_of_lt (hrz i)))
          (by rw [hij]; exact mem_closedBall_self (le_of_lt (hrz j))))
    (by rw [hset_eq]; exact hcont)
    (fun z hz => hdiff z (by rwa [hset_eq] at hz))
    hgz_ne hgz_hol hgz_cont hf_zero hf_zero_nhds
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j)


  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at key
  exact key

theorem logDeriv_circleIntegrable_of_differentiableOn {c : ℂ} {R : ℝ}
    (hR : 0 < R) {f : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hf_ne : ∀ z ∈ sphere c R, f z ≠ 0) :
    CircleIntegrable (logDeriv f) c R := by
  apply ContinuousOn.circleIntegrable hR.le
  have hf_cont : ContinuousOn f (closedBall c R) :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hderiv_cont : ContinuousOn (deriv f) (closedBall c R) :=
    continuousOn_deriv_of_differentiableAt_closedBall hR hf
  have : logDeriv f = (deriv f) / f := by ext x; simp [logDeriv_apply]
  rw [this]
  exact (hderiv_cont.mono sphere_subset_closedBall).div
    (hf_cont.mono sphere_subset_closedBall) (fun z hz => hf_ne z hz)


lemma analyticAt_of_mem_ball_of_closedBall {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z) {a : ℂ} (ha : a ∈ ball c R) :
    AnalyticAt ℂ f a :=
  Complex.analyticAt_iff_eventually_differentiableAt.mpr
    (eventually_of_mem (isOpen_ball.mem_nhds ha) (fun w hw => hf w (ball_subset_closedBall hw)))

lemma analyticOrderAt_ne_top_in_ball {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hf_ne : ∀ z ∈ sphere c R, f z ≠ 0)
    {a : ℂ} (ha : a ∈ ball c R) :
    analyticOrderAt f a ≠ ⊤ := by
  have ⟨w, hw, hfw⟩ : ∃ w ∈ ball c R, f w ≠ 0 := by
    by_contra h_all; push Not at h_all
    have hcont : ContinuousOn f (closedBall c R) :=
      fun z hz => (hf z hz).continuousAt.continuousWithinAt
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∈ sphere c R := ⟨c + R, by simp [abs_of_pos hR]⟩
    apply hf_ne w₀ hw₀
    have hw₀_cl : w₀ ∈ closure (ball c R) := by
      rw [closure_ball c (ne_of_gt hR)]; exact sphere_subset_closedBall hw₀
    have hmaps : MapsTo f (ball c R) {(0 : ℂ)} := fun z hz => h_all z hz
    have hm := hmaps.closure_of_continuousOn (by rwa [closure_ball c (ne_of_gt hR)]) hw₀_cl
    rw [closure_singleton] at hm; exact hm
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun z hz => analyticAt_of_mem_ball_of_closedBall hf hz)
    (Metric.isConnected_ball hR).isPreconnected hw ha
    (fun h => hfw (analyticOrderAt_eq_top.mp h).self_of_nhds)

lemma factorization_on_ball {f : ℂ → ℂ} {a : ℂ}
    (ha : AnalyticAt ℂ f a) (h_ne_top : analyticOrderAt f a ≠ ⊤) :
    ∃ g : ℂ → ℂ, ∃ ε : ℝ, 0 < ε ∧
      g a ≠ 0 ∧
      (∀ z, dist z a < ε → f z = (z - a) ^ analyticOrderNatAt f a * g z) ∧
      (∀ z, dist z a < ε → g z ≠ 0) ∧
      (∀ z, dist z a < ε → DifferentiableAt ℂ g z) := by
  obtain ⟨g, hga, hgne, hfg⟩ := ha.analyticOrderAt_ne_top.mp h_ne_top
  obtain ⟨ε₁, hε₁, hfg_ball⟩ := Metric.eventually_nhds_iff.mp hfg
  obtain ⟨ε₂, hε₂, hg_ne_ball⟩ := Metric.eventually_nhds_iff.mp
    (hga.continuousAt.eventually_ne hgne)
  obtain ⟨p, hp⟩ := hga
  obtain ⟨ε₃, hε₃, hg_diff_ball⟩ := Metric.eventually_nhds_iff.mp hp.eventually_differentiableAt
  refine ⟨g, min ε₁ (min ε₂ ε₃), by positivity, hgne, ?_, ?_, ?_⟩
  · intro z hz
    have := hfg_ball (lt_of_lt_of_le hz (min_le_left _ _))
    simp only [smul_eq_mul] at this; exact this
  · intro z hz
    exact hg_ne_ball (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _)))
  · intro z hz
    exact hg_diff_ball (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _)))

theorem argument_principle_zero_count {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hf_ne : ∀ z ∈ sphere c R, f z ≠ 0)
    (hf_zeros : Set.Finite {z ∈ ball c R | f z = 0}) :
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) =
    ↑(∑ᶠ z ∈ {z ∈ ball c R | f z = 0}, (analyticOrderNatAt f z : ℤ)) := by

  let S := hf_zeros.toFinset
  have hS_eq : (↑S : Set ℂ) = {z ∈ ball c R | f z = 0} := hf_zeros.coe_toFinset
  have hfinsum_eq : (∑ᶠ z ∈ {z ∈ ball c R | f z = 0}, (analyticOrderNatAt f z : ℤ)) =
      ∑ z ∈ S, (analyticOrderNatAt f z : ℤ) := by
    conv_lhs => rw [show {z ∈ ball c R | f z = 0} = ↑S from hS_eq.symm]
    exact finsum_mem_coe_finset _ _
  rw [hfinsum_eq]

  by_cases hS_empty : S = ∅
  ·
    simp only [hS_empty, Finset.sum_empty, Int.cast_zero]
    suffices h : ∮ z in C(c, R), logDeriv f z = 0 by rw [h, mul_zero]
    have hf_ne_all : ∀ z ∈ closedBall c R, f z ≠ 0 := by
      intro z hz hfz
      by_cases hzb : z ∈ ball c R
      · have hzS : z ∈ S := hf_zeros.mem_toFinset.mpr ⟨hzb, hfz⟩
        simp [hS_empty] at hzS
      · rw [mem_closedBall] at hz; rw [mem_ball] at hzb; push Not at hzb
        exact hf_ne z (mem_sphere.mpr (le_antisymm hz hzb)) hfz
    exact circleIntegral_logDeriv_eq_zero hR hf
      (fun z hz => (hf z hz).continuousAt.continuousWithinAt) hf_ne_all
  ·
    have hS_ne : S.Nonempty := Finset.nonempty_of_ne_empty hS_empty
    let n := S.card
    have hn_pos : 0 < n := Finset.card_pos.mpr hS_ne
    let e := S.equivFin
    let zeros : Fin n → ℂ := fun j => (e.symm j : ℂ)

    have hzeros_mem : ∀ j, zeros j ∈ S := fun j => (e.symm j).prop
    have hzeros_in_ball : ∀ j, zeros j ∈ ball c R :=
      fun j => (hf_zeros.mem_toFinset.mp (hzeros_mem j)).1
    have hzeros_fz : ∀ j, f (zeros j) = 0 :=
      fun j => (hf_zeros.mem_toFinset.mp (hzeros_mem j)).2
    have hzeros_inj : Function.Injective zeros :=
      fun i j hij => e.symm.injective (Subtype.val_injective hij)
    have hzeros_surj : ∀ z, z ∈ S → ∃ j, zeros j = z := by
      intro z hz; exact ⟨e ⟨z, hz⟩, by simp [zeros]⟩

    have h_ne_top : ∀ j, analyticOrderAt f (zeros j) ≠ ⊤ :=
      fun j => analyticOrderAt_ne_top_in_ball hR hf hf_ne (hzeros_in_ball j)
    have h_ana : ∀ j, AnalyticAt ℂ f (zeros j) :=
      fun j => analyticAt_of_mem_ball_of_closedBall hf (hzeros_in_ball j)
    choose gz εz hεz_pos hgz_ne_a hfact_eq hgz_ne hgz_diff
      using fun j => factorization_on_ball (h_ana j) (h_ne_top j)

    have hmult_pos : ∀ j, 0 < analyticOrderNatAt f (zeros j) := by
      intro j; by_contra h; push Not at h
      have h0 := Nat.eq_zero_of_le_zero h
      have := hfact_eq j (zeros j) (by simp [hεz_pos j])
      rw [h0, pow_zero, one_mul] at this
      exact hgz_ne_a j (this ▸ hzeros_fz j)

    have hbd_pos : ∀ j, 0 < R - dist (zeros j) c :=
      fun j => by linarith [mem_ball.mp (hzeros_in_ball j)]
    have hdist_pos : ∀ i j : Fin n, i ≠ j → 0 < dist (zeros i) (zeros j) :=
      fun i j hij => dist_pos.mpr (fun h => hij (hzeros_inj h))

    let rz : Fin n → ℝ := fun j =>
      Finset.univ.inf' ⟨j, Finset.mem_univ _⟩
        (fun k => if k = j then min (εz j / 2) ((R - dist (zeros j) c) / 2)
                  else min (min (εz j / 2) ((R - dist (zeros j) c) / 2))
                           (dist (zeros j) (zeros k) / 3))

    have hrz_le_min : ∀ j, rz j ≤ min (εz j / 2) ((R - dist (zeros j) c) / 2) := by
      intro j
      have h := Finset.inf'_le (fun k => if k = j then min (εz j / 2) ((R - dist (zeros j) c) / 2)
                  else min (min (εz j / 2) ((R - dist (zeros j) c) / 2))
                           (dist (zeros j) (zeros k) / 3)) (Finset.mem_univ j)
      simp only [ite_true] at h; exact h

    have hrz_pos : ∀ j, 0 < rz j := by
      intro j
      apply (Finset.lt_inf'_iff _).mpr; intro k _
      split_ifs with hkj
      · exact lt_min (half_pos (hεz_pos j)) (half_pos (hbd_pos j))
      · exact lt_min (lt_min (half_pos (hεz_pos j)) (half_pos (hbd_pos j)))
          (div_pos (hdist_pos j k (Ne.symm hkj)) (by norm_num))

    have hrz_lt_εz : ∀ j, rz j < εz j := by
      intro j
      have h1 := hrz_le_min j
      have h2 : rz j ≤ εz j / 2 := h1.trans (min_le_left _ _)
      linarith [hεz_pos j]

    have hrz_le_bd : ∀ j, rz j ≤ (R - dist (zeros j) c) / 2 := by
      intro j; exact (hrz_le_min j).trans (min_le_right _ _)

    have hrz_le_dist : ∀ i j, i ≠ j → rz i ≤ dist (zeros i) (zeros j) / 3 := by
      intro i j hij
      have h1 := Finset.inf'_le (fun k => if k = i then min (εz i / 2) ((R - dist (zeros i) c) / 2)
                  else min (min (εz i / 2) ((R - dist (zeros i) c) / 2))
                           (dist (zeros i) (zeros k) / 3)) (Finset.mem_univ j)
      simp only [hij.symm, ↓reduceIte] at h1
      exact h1.trans (min_le_right _ _)

    have hrz_sub : ∀ j, closedBall (zeros j) (rz j) ⊆ ball c R := by
      intro j z hz; rw [mem_closedBall] at hz; rw [mem_ball]
      calc dist z c ≤ dist z (zeros j) + dist (zeros j) c := dist_triangle _ _ _
        _ ≤ rz j + dist (zeros j) c := by linarith
        _ ≤ (R - dist (zeros j) c) / 2 + dist (zeros j) c := by linarith [hrz_le_bd j]
        _ < R := by linarith [hbd_pos j]

    have hdisj : ∀ i j : Fin n, i ≠ j →
        Disjoint (closedBall (zeros i) (rz i)) (closedBall (zeros j) (rz j)) := by
      intro i j hij; rw [Set.disjoint_iff]; intro z ⟨hi, hj⟩
      rw [mem_closedBall] at hi hj
      have htri := dist_triangle_left (zeros i) (zeros j) z
      have hdi := hrz_le_dist i j hij
      have hdj := hrz_le_dist j i hij.symm
      rw [dist_comm (zeros j) (zeros i)] at hdj
      nlinarith [hdist_pos i j hij]

    have hgz_ne_ball : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j), gz j z ≠ 0 :=
      fun j z hz => hgz_ne j z (lt_of_le_of_lt (mem_closedBall.mp hz) (hrz_lt_εz j))
    have hgz_hol_ball : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j), DifferentiableAt ℂ (gz j) z :=
      fun j z hz => hgz_diff j z (lt_of_le_of_lt (mem_closedBall.mp hz) (hrz_lt_εz j))
    have hgz_cont_ball : ∀ j, ContinuousOn (gz j) (closedBall (zeros j) (rz j)) :=
      fun j z hz => (hgz_hol_ball j z hz).continuousAt.continuousWithinAt

    have hf_zero : ∀ j, ∀ z ∈ closedBall (zeros j) (rz j) \ {zeros j},
        f z = (z - zeros j) ^ analyticOrderNatAt f (zeros j) * gz j z :=
      fun j z ⟨hz, _⟩ => hfact_eq j z (lt_of_le_of_lt (mem_closedBall.mp hz) (hrz_lt_εz j))

    have hf_zero_nhds : ∀ j, ∀ z ∈ sphere (zeros j) (rz j),
        ∀ᶠ w in 𝓝 z, f w = (w - zeros j) ^ analyticOrderNatAt f (zeros j) * gz j w := by
      intro j z hz
      rw [_root_.Metric.eventually_nhds_iff]
      refine ⟨εz j - rz j, by linarith [hrz_lt_εz j], fun w hw => ?_⟩
      apply hfact_eq j
      have hzd : dist z (zeros j) = rz j := by rwa [mem_sphere] at hz
      calc dist w (zeros j) ≤ dist w z + dist z (zeros j) := dist_triangle _ _ _
        _ = dist w z + rz j := by rw [hzd]
        _ < (εz j - rz j) + rz j := by linarith [hw]
        _ = εz j := by ring

    have hzeros_range : ∀ z ∈ ball c R, f z = 0 → z ∈ ⋃ j : Fin n, {zeros j} := by
      intro z hzb hfz
      have hzS : z ∈ S := hf_zeros.mem_toFinset.mpr ⟨hzb, hfz⟩
      rw [mem_iUnion]; exact ⟨e ⟨z, hzS⟩, by simp [zeros]⟩

    have hcont : ContinuousOn (logDeriv f) (closedBall c R \ (⋃ j : Fin n, {zeros j})) := by
      have hlogDeriv_eq : logDeriv f = (deriv f) / f := by ext x; simp [logDeriv_apply]
      rw [hlogDeriv_eq]
      apply ContinuousOn.div
      · exact (continuousOn_deriv_of_differentiableAt_closedBall hR hf).mono diff_subset
      · exact ContinuousOn.mono (fun z hz => (hf z hz).continuousAt.continuousWithinAt :
          ContinuousOn f (closedBall c R)) (Set.diff_subset)
      · intro z ⟨hz_cb, hz_ne⟩ hfz
        by_cases hzb : z ∈ ball c R
        · exact hz_ne (hzeros_range z hzb hfz)
        · rw [mem_closedBall] at hz_cb; rw [mem_ball] at hzb; push Not at hzb
          exact hf_ne z (mem_sphere.mpr (le_antisymm hz_cb hzb)) hfz

    have hdiff : ∀ z ∈ ball c R \ (⋃ j : Fin n, {zeros j}),
        DifferentiableAt ℂ (logDeriv f) z := by
      intro z ⟨hz_ball, hz_ne⟩
      have h_fz_ne : f z ≠ 0 := fun hfz => hz_ne (hzeros_range z hz_ball hfz)
      have h_ana_z := analyticAt_of_mem_ball_of_closedBall hf hz_ball
      have : logDeriv f = fun w => deriv f w / f w := by ext; simp [logDeriv_apply]
      rw [this]
      exact h_ana_z.deriv.differentiableAt.div h_ana_z.differentiableAt h_fz_ne

    have key := argument_principle_no_poles hR
      (zeros := zeros) (multZ := fun j => analyticOrderNatAt f (zeros j))
      (rz := rz) (gz := gz)
      hzeros_in_ball hrz_pos hmult_pos hrz_sub hdisj
      hcont hdiff hgz_ne_ball hgz_hol_ball hgz_cont_ball hf_zero hf_zero_nhds

    rw [key]; congr 1

    exact Finset.sum_nbij zeros
      (fun j _ => hzeros_mem j)
      (fun i _ j _ hij => hzeros_inj hij)
      (fun z hz => by
        obtain ⟨j, hj⟩ := hzeros_surj z hz
        exact ⟨j, Finset.mem_univ _, hj⟩)
      (fun _ _ => rfl)

theorem rouche_integral_eq_of_differentiableOn {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f g : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hg : ∀ z ∈ closedBall c R, DifferentiableAt ℂ g z)
    (hbound : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖)
    (hf_int : CircleIntegrable (logDeriv f) c R)
    (hg_int : CircleIntegrable (logDeriv g) c R) :
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv g z) =
    (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) :=
  rouche_integral_eq hR hf hg hbound hf_int hg_int

theorem rouche_theorem {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f g : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hg : ∀ z ∈ closedBall c R, DifferentiableAt ℂ g z)
    (hf_ne : ∀ z ∈ sphere c R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖)
    (hf_zeros : Set.Finite {z ∈ ball c R | f z = 0})
    (hg_zeros : Set.Finite {z ∈ ball c R | g z = 0}) :
    ∑ᶠ z ∈ {z ∈ ball c R | f z = 0}, (analyticOrderNatAt f z : ℤ) =
    ∑ᶠ z ∈ {z ∈ ball c R | g z = 0}, (analyticOrderNatAt g z : ℤ) := by


  have hg_ne : ∀ z ∈ sphere c R, g z ≠ 0 := by
    intro z hz hgz
    have hbd := hbound z hz
    rw [hgz, sub_zero] at hbd
    exact lt_irrefl _ hbd

  have hf_int := logDeriv_circleIntegrable_of_differentiableOn hR hf hf_ne
  have hg_int := logDeriv_circleIntegrable_of_differentiableOn hR hg hg_ne

  have hAP_f := argument_principle_zero_count hR hf hf_ne hf_zeros
  have hAP_g := argument_principle_zero_count hR hg hg_ne hg_zeros

  have hIntEq := rouche_integral_eq_of_differentiableOn hR hf hg hbound hf_int hg_int


  have : (↑(∑ᶠ z ∈ {z ∈ ball c R | f z = 0}, (analyticOrderNatAt f z : ℤ)) : ℂ) =
         ↑(∑ᶠ z ∈ {z ∈ ball c R | g z = 0}, (analyticOrderNatAt g z : ℤ)) := by
    rw [← hAP_f, ← hAP_g, hIntEq]
  exact_mod_cast this

end
