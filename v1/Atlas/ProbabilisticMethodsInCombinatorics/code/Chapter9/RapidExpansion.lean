/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.HarperIsoperimetric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Floor.Semiring
set_option maxHeartbeats 800000

open Finset Real HarperIsoperimetric

namespace RapidExpansion

/-- The **Hamming weight** of $x \in \{0, 1\}^n$, i.e. the number of coordinates equal to
`true`; defined as the Hamming distance from the all-`false` vector. -/
def hammingWt {n : ℕ} (x : HammingCube n) : ℕ :=
  hammingDist x (fun _ => false)

/-- The **open Hamming ball** of radius $r$ centred at the origin in $\{0, 1\}^n$:
$\{x : \operatorname{wt}(x) < r\}$. -/
def openHammingBall (n : ℕ) (r : ℕ) : Finset (HammingCube n) :=
  Finset.univ.filter (fun x => hammingWt x < r)

/-- The **bit-flip involution** on the Hamming cube: $(\operatorname{flip}(x))_i = \neg x_i$
for every coordinate $i$. -/
def bitFlip (n : ℕ) (x : HammingCube n) : HammingCube n :=
  fun i => !(x i)

/-- The bit-flip map is an involution: $\operatorname{flip}(\operatorname{flip}(x)) = x$. -/
lemma bitFlip_bitFlip (n : ℕ) (x : HammingCube n) : bitFlip n (bitFlip n x) = x := by
  funext i
  simp [bitFlip]

/-- Flipping all bits complements the weight: $\operatorname{wt}(\operatorname{flip}(x)) =
n - \operatorname{wt}(x)$. -/
lemma hammingWt_bitFlip (n : ℕ) (x : HammingCube n) :
    hammingWt (bitFlip n x) = n - hammingWt x := by
  simp only [hammingWt, hammingDist, bitFlip]


  convert_to (Finset.univ.filter fun i : Fin n => x i ≠ false)ᶜ.card =
    n - (Finset.univ.filter fun i : Fin n => x i ≠ false).card
  · congr 1
    ext i
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    cases x i <;> simp
  · rw [Finset.card_compl, Fintype.card_fin]

/-- The bit-flip map is injective (in fact, a bijection, since it is its own inverse). -/
lemma bitFlip_injective (n : ℕ) : Function.Injective (bitFlip n) := by
  intro x y hxy
  have := congr_arg (bitFlip n) hxy
  rwa [bitFlip_bitFlip, bitFlip_bitFlip] at this

/-- The Hamming ball of radius $\lfloor n/2 \rfloor$ contains at most half of the cube:
$|B(n, n/2)| \le 2^{n-1}$. The proof uses bit-flipping to inject the ball into its
complement. -/
lemma card_openHammingBall_le (n : ℕ) :
    (openHammingBall n (n / 2)).card ≤ 2 ^ (n - 1) := by
  by_cases hn : n = 0
  · subst hn; simp [openHammingBall]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn

  suffices h : (openHammingBall n (n / 2)).card ≤
      (Finset.univ \ openHammingBall n (n / 2)).card by
    have huniv : (Finset.univ : Finset (HammingCube n)).card = 2 ^ n := by
      simp [Fintype.card_pi, Fintype.card_bool]
    have hsdiff := Finset.card_sdiff_of_subset
      (Finset.subset_univ (openHammingBall n (n / 2)))
    rw [huniv] at hsdiff
    have h_pow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      have hn1 : n = n - 1 + 1 := by omega
      conv_rhs => rw [hn1, pow_succ]
      ring
    omega

  apply Finset.card_le_card_of_injOn (bitFlip n)
  ·
    intro x hx
    have hx' : hammingWt x < n / 2 := by
      simp only [openHammingBall, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      exact hx
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      openHammingBall, Finset.mem_filter, not_lt]
    rw [hammingWt_bitFlip]
    omega
  ·
    intro x _ y _ hxy
    exact bitFlip_injective n hxy

/-- The open Hamming ball of radius $n/2$ around the origin coincides with the closed
Hamming ball of radius $n/2 - 1$, hence is a "Hamming ball" in the Harper sense. -/
lemma openHammingBall_isHammingBall (n : ℕ) (hr : 0 < n / 2) :
    IsHammingBall (openHammingBall n (n / 2)) := by
  refine ⟨fun _ => false, n / 2 - 1, ?_⟩
  ext x
  simp only [openHammingBall, hammingBallFinset, hammingWt, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

/-- The $0$-expansion of a set is the set itself: $S_0 = S$. -/
lemma hammingExpansion_zero (n : ℕ) (S : Finset (HammingCube n)) :
    hammingExpansion S 0 = S := by
  ext x
  simp only [hammingExpansion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hdist⟩
    have : x = a := by
      funext i
      by_contra h
      have : 0 < (Finset.univ.filter fun j => x j ≠ a j).card := by
        apply Finset.card_pos.mpr
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      simp only [hammingDist] at hdist
      omega
    rw [this]; exact ha
  · intro hx
    exact ⟨x, hx, by simp [hammingDist]⟩

/-- The $t$-expansion of the empty set is empty. -/
lemma hammingExpansion_empty (n : ℕ) (t : ℕ) :
    hammingExpansion (∅ : Finset (HammingCube n)) t = ∅ := by
  ext x
  simp [hammingExpansion]

/-- Specialization of Harper's vertex-isoperimetric inequality: any $A \subseteq \{0, 1\}^n$
with $|A| \ge 2^{n-1}$ has $t$-expansion at least as large as that of the Hamming ball of
radius $\lfloor n/2 \rfloor$. -/
theorem harper_applied (n : ℕ) (t : ℕ)
    (A : Finset (HammingCube n))
    (hA : 2 ^ (n - 1) ≤ A.card) :
    (hammingExpansion (openHammingBall n (n / 2)) t).card ≤ (hammingExpansion A t).card := by

  have hcard_ball : (openHammingBall n (n / 2)).card ≤ A.card :=
    le_trans (card_openHammingBall_le n) hA
  rcases t with _ | t
  ·
    rw [hammingExpansion_zero, hammingExpansion_zero]
    exact hcard_ball
  ·
    have ht : 0 < t + 1 := Nat.succ_pos t
    by_cases hn2 : n / 2 = 0
    ·
      have h_empty : openHammingBall n (n / 2) = ∅ := by
        rw [hn2]
        ext x
        simp [openHammingBall, hammingWt]
      rw [h_empty, hammingExpansion_empty]
      exact Nat.zero_le _
    ·
      have hn2_pos : 0 < n / 2 := Nat.pos_of_ne_zero hn2
      exact harper_isoperimetric_inequality A (openHammingBall n (n / 2))
        (openHammingBall_isHammingBall n hn2_pos) hcard_ball (t + 1) ht

/-- The Hamming weight equals the number of `true` coordinates: $\operatorname{wt}(x) =
|\{i : x_i = \text{true}\}|$. -/
theorem hammingWt_eq_filter_card {n : ℕ} (x : HammingCube n) :
    hammingWt x = (Finset.univ.filter (fun i => x i = true)).card := by
  unfold hammingWt hammingDist
  congr 1
  ext i
  simp

/-- The Hamming distance from any point to itself is zero. -/
theorem hammingDist_self_eq_zero {n : ℕ} (x : HammingCube n) : hammingDist x x = 0 := by
  unfold hammingDist; simp

/-- Triangle-style inequality for the Hamming weight:
$\operatorname{wt}(x) \le \operatorname{wt}(y) + d(x, y)$. -/
theorem hammingWt_le_add_dist {n : ℕ} (x y : HammingCube n) :
    hammingWt x ≤ hammingWt y + hammingDist x y := by
  unfold hammingWt
  suffices h : hammingDist x (fun _ => false) ≤ hammingDist x y + hammingDist y (fun _ => false) by
    omega
  unfold hammingDist
  apply le_trans (Finset.card_le_card _) (Finset.card_union_le _ _)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  intro hxz
  by_cases hxy : x i ≠ y i
  · left; exact hxy
  · right; push Not at hxy; rw [hxy] at hxz; exact hxz

/-- Flipping a subset $T$ of the $1$-coordinates of $x$ to $0$ produces a vector $y$ at
Hamming distance $|T|$ from $x$ and of weight $\operatorname{wt}(x) - |T|$. -/
theorem flip_dist_and_wt {n : ℕ} (x : HammingCube n) (T : Finset (Fin n))
    (hT : T ⊆ Finset.univ.filter (fun i => x i = true)) :
    let y : HammingCube n := fun i => if i ∈ T then false else x i
    hammingDist x y = T.card ∧ hammingWt y = hammingWt x - T.card := by
  constructor
  · unfold hammingDist
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hne
      by_contra hni
      simp only [hni, ite_false] at hne
      exact hne rfl
    · intro hi
      have hxi : x i = true := by
        have hmem := hT hi
        rw [Finset.mem_filter] at hmem
        exact hmem.2
      simp [hi, hxi]
  · rw [hammingWt_eq_filter_card, hammingWt_eq_filter_card]
    suffices h : (Finset.univ.filter (fun i => (if i ∈ T then false else x i) = true)) =
        (Finset.univ.filter (fun i => x i = true)) \ T by
      rw [h, Finset.card_sdiff_of_subset hT]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hi
      exact ⟨h, hi⟩
    · intro ⟨hxi, hni⟩
      simp [hni, hxi]

/-- The $t$-expansion of the Hamming ball $B(n, n/2)$ is the Hamming ball
$B(n, n/2 + t)$ of larger radius. -/
theorem expansion_openBall (n : ℕ) (t : ℕ) (hn : 1 < n) :
    hammingExpansion (openHammingBall n (n / 2)) t = openHammingBall n (n / 2 + t) := by
  ext x
  simp only [hammingExpansion, openHammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hd⟩
    have hwt := hammingWt_le_add_dist x a
    omega
  · intro hx
    by_cases h : hammingWt x < n / 2
    · exact ⟨x, h, by rw [hammingDist_self_eq_zero]; omega⟩
    · push Not at h
      have hn2 : 0 < n / 2 := Nat.div_pos (by omega) (by omega)
      have hk_le_t : hammingWt x - n / 2 + 1 ≤ t := by omega
      have hk_le_S : hammingWt x - n / 2 + 1 ≤
          (Finset.univ.filter (fun i : Fin n => x i = true)).card := by
        rw [← hammingWt_eq_filter_card]; omega
      obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hk_le_S
      refine ⟨fun i => if i ∈ T then false else x i, ?_, ?_⟩
      · have ⟨_, hwt⟩ := flip_dist_and_wt x T hT_sub
        rw [hwt, hT_card]; omega
      · have ⟨hdist, _⟩ := flip_dist_and_wt x T hT_sub
        rw [hdist, hT_card]; omega

/-- **Chernoff upper-tail bound** for the cardinality of the heavy slice of the cube:
the number of points $x \in \{0, 1\}^n$ with $\operatorname{wt}(x) \ge n/2 + t$ is strictly
less than $e^{-2t^{2}/n} \cdot 2^{n}$. -/
theorem chernoff_upper_tail_card (n : ℕ) (t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    ((Finset.univ.filter (fun x : HammingCube n => n / 2 + t ≤ hammingWt x)).card : ℝ) <
      exp (-2 * (t : ℝ) ^ 2 / (n : ℝ)) * 2 ^ n := by sorry

/-- Chernoff-type lower bound on the size of the Hamming ball:
$|B(n, n/2 + t)| > (1 - e^{-2t^{2}/n}) \cdot 2^{n}$. -/
theorem chernoff_hamming_ball (n : ℕ) (t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    (1 - exp (-2 * (t : ℝ) ^ 2 / (n : ℝ))) * 2 ^ n <
      ((openHammingBall n (n / 2 + t)).card : ℝ) := by
  have h_card_univ : (Finset.univ : Finset (HammingCube n)).card = 2 ^ n := by
    simp [Fintype.card_pi, Fintype.card_bool]

  set ball := openHammingBall n (n / 2 + t)
  set compl := Finset.univ.filter (fun x : HammingCube n => n / 2 + t ≤ hammingWt x)
  have h_disj : Disjoint ball compl := by
    simp only [ball, compl, openHammingBall, Finset.disjoint_left]
    intro x hx hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hc
    omega
  have h_union : ball ∪ compl = Finset.univ := by
    ext x
    simp only [ball, compl, openHammingBall, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => Nat.lt_or_ge (hammingWt x) (n / 2 + t)⟩
  have h_partition : ball.card + compl.card = 2 ^ n := by
    have := Finset.card_union_of_disjoint h_disj
    linarith [show (ball ∪ compl).card = 2 ^ n from by rw [h_union, h_card_univ]]

  have h_tail := chernoff_upper_tail_card n t hn ht

  have h_ball_eq : (ball.card : ℝ) = 2 ^ n - (compl.card : ℝ) := by
    have h := h_partition
    have : (ball.card : ℝ) + (compl.card : ℝ) = (2 : ℝ) ^ n := by
      exact_mod_cast h
    linarith
  linarith

/-- **Rapid expansion from half to $1 - \varepsilon$** (Theorem 9.4.5). For any
$A \subseteq \{0, 1\}^n$ with $|A| \ge 2^{n-1}$ and any $t \ge 1$, the $t$-expansion satisfies
$|A_t| > (1 - e^{-2t^{2}/n}) \cdot 2^{n}$. -/
theorem rapid_expansion_half_to_one_minus_eps (n : ℕ) (hn : 1 < n) (t : ℕ) (ht : 0 < t)

    (A : Finset (HammingCube n))
    (hA : 2 ^ (n - 1) ≤ A.card) :
    (1 - exp (-2 * (t : ℝ) ^ 2 / (n : ℝ))) * 2 ^ n <
      ((hammingExpansion A t).card : ℝ) := by
  calc (1 - exp (-2 * (t : ℝ) ^ 2 / (n : ℝ))) * 2 ^ n
      < ((openHammingBall n (n / 2 + t)).card : ℝ) :=
        chernoff_hamming_ball n t (by omega) ht
    _ = ((hammingExpansion (openHammingBall n (n / 2)) t).card : ℝ) := by
        rw [expansion_openBall n t hn]
    _ ≤ ((hammingExpansion A t).card : ℝ) := by
        exact_mod_cast harper_applied n t A hA

/-- Hamming distance is symmetric: $d(x, y) = d(y, x)$. -/
theorem hammingDist_symm {n : ℕ} (x y : HammingCube n) :
    hammingDist x y = hammingDist y x := by
  simp only [hammingDist]
  congr 1
  ext i
  simp [Ne, eq_comm]

/-- **Triangle inequality** for the Hamming distance: $d(x, z) \le d(x, y) + d(y, z)$. -/
theorem hammingDist_triangle {n : ℕ} (x y z : HammingCube n) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  unfold hammingDist
  apply le_trans (Finset.card_le_card _) (Finset.card_union_le _ _)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  intro hxz
  by_cases hxy : x i ≠ y i
  · left; exact hxy
  · right
    push Not at hxy
    rw [hxy] at hxz
    exact hxz

/-- The $t$-expansion of the complement of $A_t$ is disjoint from $A$: any point reachable
within distance $t$ from outside $A_t$ cannot lie in $A$ itself. -/
theorem expansion_complement_disjoint_of_A {n : ℕ} (A : Finset (HammingCube n)) (t : ℕ) :
    Disjoint (hammingExpansion (Finset.univ \ hammingExpansion A t) t) A := by
  rw [Finset.disjoint_left]
  intro x hx_exp hx_A
  simp only [hammingExpansion, Finset.mem_filter, Finset.mem_univ, true_and] at hx_exp
  obtain ⟨a', ha'_compl, hdist_xa'⟩ := hx_exp
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_filter] at ha'_compl
  have h_not : ¬(∃ a ∈ A, hammingDist a' a ≤ t) := ha'_compl
  have h_gt : t < hammingDist a' x := by
    by_contra h
    push Not at h
    exact h_not ⟨x, hx_A, h⟩
  rw [hammingDist_symm] at h_gt
  omega

/-- The iterated expansion is contained in a single larger expansion:
$(A_s)_t \subseteq A_{s + t}$. -/
theorem expansion_expansion_subset {n : ℕ} (A : Finset (HammingCube n)) (s t : ℕ) :
    hammingExpansion (hammingExpansion A s) t ⊆ hammingExpansion A (s + t) := by
  intro x hx
  simp only [hammingExpansion, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨a, ha, hya⟩ := hy
  exact ⟨a, ha, le_trans (hammingDist_triangle x y a) (by omega)⟩

/-- The Hamming cube $\{0, 1\}^n$ has exactly $2^n$ elements. -/
theorem card_univ_hammingCube (n : ℕ) :
    (Finset.univ : Finset (HammingCube n)).card = 2 ^ n := by
  simp [Fintype.card_pi, Fintype.card_bool]

/-- Bootstrap lemma: if $|A| \ge e^{-2t^{2}/n} \cdot 2^{n}$, then the $t$-expansion of $A$
already has size at least $2^{n-1}$. -/
theorem expansion_card_half (n : ℕ) (hn : 1 < n) (t : ℕ) (ht : 0 < t)
    (A : Finset (HammingCube n))
    (hA : exp (-2 * (t : ℝ) ^ 2 / (n : ℝ)) * 2 ^ n ≤ (A.card : ℝ)) :
    2 ^ (n - 1) ≤ (hammingExpansion A t).card := by
  by_contra h_lt
  push Not at h_lt

  set At := hammingExpansion A t with hAt_def
  set A' := Finset.univ \ At with hA'_def
  have h_card_At : At.card < 2 ^ (n - 1) := h_lt
  have h_card_A' : 2 ^ (n - 1) ≤ A'.card := by
    rw [hA'_def]
    have h_univ_card : (Finset.univ : Finset (HammingCube n)).card = 2 ^ n :=
      card_univ_hammingCube n
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ At), h_univ_card]
    have h_pow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      have : n = n - 1 + 1 := by omega
      conv_rhs => rw [this, pow_succ]
      ring
    omega

  have h_thm95 := rapid_expansion_half_to_one_minus_eps n hn t ht A' h_card_A'

  have h_disj : Disjoint (hammingExpansion A' t) A :=
    expansion_complement_disjoint_of_A A t

  have h_union := Finset.card_union_of_disjoint h_disj
  have h_le_univ : (hammingExpansion A' t ∪ A).card ≤ 2 ^ n := by
    have := Finset.card_le_card
      (Finset.subset_univ (hammingExpansion A' t ∪ A))
    rw [card_univ_hammingCube] at this
    exact this
  have h_nat : (hammingExpansion A' t).card + A.card ≤ 2 ^ n := by omega
  have h_real : ((hammingExpansion A' t).card : ℝ) + (A.card : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast h_nat

  linarith

/-- **Rapid expansion from $\varepsilon$ to $1 - \varepsilon$** (Theorem 9.4.6). If
$|A| \ge e^{-2t^{2}/n} \cdot 2^{n}$, then $|A_{2t}| \ge (1 - e^{-2t^{2}/n}) \cdot 2^{n}$. -/
theorem rapid_expansion_eps_to_one_minus_eps (n : ℕ) (hn : 1 < n) (t : ℕ) (ht : 0 < t)
    (A : Finset (HammingCube n))
    (hA : exp (-2 * (t : ℝ) ^ 2 / (n : ℝ)) * 2 ^ n ≤ (A.card : ℝ)) :
    (1 - exp (-2 * (t : ℝ) ^ 2 / (n : ℝ))) * 2 ^ n ≤
      ((hammingExpansion A (2 * t)).card : ℝ) := by

  have h_half := expansion_card_half n hn t ht A hA

  have h_thm95 := rapid_expansion_half_to_one_minus_eps n hn t ht
    (hammingExpansion A t) h_half

  have h_subset := expansion_expansion_subset A t t
  have h_card_le : (hammingExpansion (hammingExpansion A t) t).card ≤
      (hammingExpansion A (2 * t)).card := by
    apply Finset.card_le_card
    convert h_subset using 2
    omega

  have h_cast : ((hammingExpansion (hammingExpansion A t) t).card : ℝ) ≤
      ((hammingExpansion A (2 * t)).card : ℝ) := by
    exact_mod_cast h_card_le
  linarith

/-- **Rapid expansion in the Hamming cube** (continuous form). If $|A| \ge \varepsilon \cdot 2^{n}$
for some $\varepsilon \in (0, 1)$, then for $t = \lceil \sqrt{\log(1/\varepsilon) \cdot n / 2}
\rceil$, $|A_{2t}| \ge (1 - \varepsilon) \cdot 2^{n}$. -/
theorem rapid_expansion_hamming (n : ℕ) (hn : 1 < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (A : Finset (HammingCube n))
    (hA : (A.card : ℝ) ≥ ε * 2 ^ n) :
    let C := Real.sqrt (2 * Real.log (1 / ε))
    ((hammingExpansion A (2 * ⌈Real.sqrt (Real.log (1 / ε) * ↑n / 2)⌉₊)).card : ℝ) ≥
      (1 - ε) * 2 ^ n := by
  intro C
  set t := ⌈Real.sqrt (Real.log (1 / ε) * ↑n / 2)⌉₊
  have hlog_pos : 0 < Real.log (1 / ε) := Real.log_pos (by
    rw [one_div]
    exact one_lt_inv_iff₀.mpr ⟨hε, hε1⟩)
  have hn_pos : (0 : ℝ) < (↑n : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n)
  have harg_pos : 0 < Real.log (1 / ε) * ↑n / 2 := by positivity
  have ht_pos : 0 < t := Nat.ceil_pos.mpr (Real.sqrt_pos_of_pos harg_pos)


  have ht_ge : (t : ℝ) ≥ Real.sqrt (Real.log (1 / ε) * ↑n / 2) :=
    Nat.le_ceil _
  have ht_sq : (t : ℝ) ^ 2 ≥ Real.log (1 / ε) * ↑n / 2 := by
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Real.log (1 / ε) * ↑n / 2) :=
      Real.sqrt_nonneg _
    have ht_nn : (0 : ℝ) ≤ (t : ℝ) := by positivity
    nlinarith [sq_nonneg ((t : ℝ) - Real.sqrt (Real.log (1 / ε) * ↑n / 2)),
              Real.sq_sqrt (le_of_lt harg_pos)]
  have hexp_le : Real.exp (-2 * (t : ℝ) ^ 2 / ↑n) ≤ ε := by
    have h1 : Real.log (1 / ε) * ↑n ≤ 2 * (t : ℝ) ^ 2 := by linarith
    have h2 : -2 * (t : ℝ) ^ 2 / ↑n ≤ -Real.log (1 / ε) := by
      have h1' : Real.log (1 / ε) ≤ 2 * (t : ℝ) ^ 2 / ↑n := by
        rwa [le_div_iff₀ hn_pos]
      have : -2 * (t : ℝ) ^ 2 / ↑n = -(2 * (t : ℝ) ^ 2 / ↑n) := by ring
      linarith
    have h3 : Real.exp (-2 * (t : ℝ) ^ 2 / ↑n) ≤ Real.exp (-Real.log (1 / ε)) :=
      Real.exp_le_exp.mpr h2
    have h4 : Real.exp (-Real.log (1 / ε)) = ε := by
      rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 1/ε)]
      simp [one_div]
    linarith

  have hA_hyp : exp (-2 * (t : ℝ) ^ 2 / ↑n) * 2 ^ n ≤ (A.card : ℝ) := by
    have h2n_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
    nlinarith

  have h_thm := rapid_expansion_eps_to_one_minus_eps n hn t ht_pos A hA_hyp


  have h2n_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have h_exp_pos : (0 : ℝ) < Real.exp (-2 * (t : ℝ) ^ 2 / ↑n) := Real.exp_pos _
  nlinarith [hexp_le, h2n_pos, h_exp_pos]

end RapidExpansion
