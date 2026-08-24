/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter8.JansonInequality

namespace ChromaticNumber

open Finset Real Filter Nat Classical

/-- Expected number of $k$-cliques in $G(n,1/2)$:
$\mu = \binom{n}{k} \cdot 2^{-\binom{k}{2}}$. -/
noncomputable def muClique (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(Nat.choose k 2 : ℤ))

/-- The largest $k \le n$ for which the expected number $\mu(n,k)$ of $k$-cliques in
$G(n,1/2)$ is still at least $1$. -/
noncomputable def k₀ (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => (1 : ℝ) ≤ muClique n k) n

/-- Clique number of a finite graph on `Fin n`: the largest $k \le n$ such that $G$
contains a clique of size $k$. -/
noncomputable def cliqueNum {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.findGreatest (fun k => ¬G.CliqueFree k) n

/-- Probability of an event $A$ on graphs sampled from $G(n,1/2)$, computed combinatorially
as the fraction of graphs on $\{1,\dots,n\}$ satisfying $A$. -/
noncomputable def probGnHalf (n : ℕ) (A : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter (fun G => A G)).card : ℝ) /
  (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- The $\Delta$ quantity from Janson's inequality applied to the $k$-clique event in
$G(n,1/2)$: a sum over the shared-vertex parameter $s \in [2, k-1]$ that bounds the
correlation between pairs of overlapping $k$-cliques. -/
noncomputable def deltaClique (n k : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 2 (k - 1),
    (Nat.choose k s : ℝ) * (Nat.choose (n - k) (k - s) : ℝ) *
    (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(2 * Nat.choose k 2 - Nat.choose s 2 : ℤ))

/-- The threshold clique-size $k_0(n)$ is at most $n$, since it is the greatest such value
in $\{0, \dots, n\}$. -/
lemma k₀_le (n : ℕ) : k₀ n ≤ n := Nat.findGreatest_le n

/-- Dual characterization of `cliqueNum`: for $0 < m \le n$, the clique number of $G$ is
strictly less than $m$ iff $G$ contains no $m$-clique. -/
lemma cliqueNum_lt_iff_cliqueFree {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ)
    (hm : m ≤ n) (hm0 : 0 < m) :
    cliqueNum G < m ↔ G.CliqueFree m := by
  simp only [cliqueNum]
  constructor
  · intro h
    by_contra habs
    exact Nat.not_lt.mpr (Nat.le_findGreatest hm habs) h
  · intro hcf
    by_contra hlt
    push_neg at hlt
    have hne : (Nat.findGreatest (fun k => ¬G.CliqueFree k) n) ≠ 0 := by omega
    exact (Nat.findGreatest_of_ne_zero rfl hne) (SimpleGraph.CliqueFree.mono hlt hcf)


/-- Parametric form of Janson's inequality applied to the $k$-clique event: for each
$q \in [0,1]$,
$\Pr_{G(n,1/2)}(G \text{ is } K_k\text{-free}) \le \exp(-q\mu + q^2 \Delta / 2)$,
with $\mu = $ `muClique n k` and $\Delta = $ `deltaClique n k`. -/
theorem janson_clique_parametric_bound
    (n k : ℕ) (hμ : 0 < muClique n k)
    (hΔ : muClique n k ≤ deltaClique n k) :
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      probGnHalf n (fun G => G.CliqueFree k) ≤
        Real.exp (-q * muClique n k + q ^ 2 * deltaClique n k / 2) := by sorry


/-- Optimized Janson bound for the $k$-clique event, obtained by minimizing the parametric
bound over $q$: $\Pr(G \text{ is } K_k\text{-free}) \le \exp(-\mu^2 / (2\Delta))$. -/
theorem janson_clique_bound
    (n k : ℕ) (hμ : 0 < muClique n k)
    (hΔ : muClique n k ≤ deltaClique n k) :
    probGnHalf n (fun G => G.CliqueFree k) ≤
      Real.exp (-(muClique n k) ^ 2 / (2 * deltaClique n k)) :=
  JansonInequality.janson_inequality_II hμ hΔ
    (janson_clique_parametric_bound n k hμ hΔ)

/-- Elementary bound $L! \le 2^{\binom{L}{2}}$, used in estimating the asymptotics of the
clique-counting quantities. -/
lemma factorial_le_two_pow_choose (L : ℕ) : L ! ≤ 2 ^ Nat.choose L 2 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    have hchoose : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
      simp [Nat.choose_succ_succ, Nat.choose_one_right]; omega
    rw [hchoose, Nat.pow_add]
    calc (n + 1) * n ! ≤ 2 ^ n * n ! := Nat.mul_le_mul_right _ n.lt_two_pow_self
      _ ≤ 2 ^ n * 2 ^ Nat.choose n 2 := Nat.mul_le_mul_left _ ih
      _ = 2 ^ Nat.choose n 2 * 2 ^ n := by ring
/-- Asymptotic lower bound on the expected clique count at the shifted threshold: for any
$\varepsilon > 0$, eventually $\mu(n, k_0(n) - 3) \ge n^{3 - \varepsilon}$. -/
theorem mu_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      (↑n : ℝ) ^ (3 - ε) ≤ muClique n (k₀ n - 3) := by sorry


/-- Asymptotic upper bound on $\Delta$ relative to $\mu^2$: for any $\varepsilon > 0$,
eventually $\Delta(n, k_0(n) - 3) \le \mu(n, k_0(n) - 3)^2 \cdot n^{-2 + \varepsilon}$. -/
theorem delta_mu_sq_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      deltaClique n (k₀ n - 3) ≤
        (muClique n (k₀ n - 3)) ^ 2 * (↑n : ℝ) ^ (-2 + ε) := by sorry


/-- Eventually the dominant $s = 2$ term of $\Delta / \mu$ is at least $1$:
$\binom{k}{2}\binom{n-k}{k-2} \cdot 2^{1 - \binom{k}{2}} \ge 1$ at $k = k_0(n) - 3$. -/
theorem delta_s2_ratio_ge_one :
    ∀ᶠ (n : ℕ) in atTop,
      (1 : ℝ) ≤ (Nat.choose (k₀ n - 3) 2 : ℝ) *
        (Nat.choose (n - (k₀ n - 3)) (k₀ n - 3 - 2) : ℝ) *
        (2 : ℝ) ^ ((1 : ℤ) - (Nat.choose (k₀ n - 3) 2 : ℤ)) := by sorry


/-- Eventually $k_0(n) \ge 6$: the threshold clique size grows without bound, in
particular it surpasses every fixed constant. -/
theorem k0_eventually_ge_six : ∀ᶠ (n : ℕ) in atTop, 6 ≤ k₀ n := by sorry


/-- Eventually $\Delta \ge \mu$ at the shifted threshold, since the $s = 2$ summand of
$\Delta$ alone dominates $\mu$. -/
theorem delta_ge_mu_eventually :
    ∀ᶠ (n : ℕ) in atTop,
      muClique n (k₀ n - 3) ≤ deltaClique n (k₀ n - 3) := by
  apply (delta_s2_ratio_ge_one.and k0_eventually_ge_six).mono
  intro n ⟨hratio_n, hk_n⟩
  set k := k₀ n - 3
  have hk3 : 3 ≤ k := by omega

  have hge_s2 : (Nat.choose k 2 : ℝ) * (Nat.choose (n - k) (k - 2) : ℝ) *
    (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(2 * (Nat.choose k 2 : ℤ) - 1)) ≤
    deltaClique n k := by
    unfold deltaClique
    have h2mem : (2 : ℕ) ∈ Finset.Icc 2 (k - 1) := by
      simp [Finset.mem_Icc]; omega
    convert Finset.single_le_sum (f := fun s => (Nat.choose k s : ℝ) *
      (Nat.choose (n - k) (k - s) : ℝ) * (Nat.choose n k : ℝ) *
      (2 : ℝ) ^ (-(2 * Nat.choose k 2 - Nat.choose s 2 : ℤ)))
      (fun s _ => by positivity) h2mem using 1

  have hfactor : (Nat.choose k 2 : ℝ) * (Nat.choose (n - k) (k - 2) : ℝ) *
    (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(2 * (Nat.choose k 2 : ℤ) - 1)) =
    muClique n k * ((Nat.choose k 2 : ℝ) * (Nat.choose (n - k) (k - 2) : ℝ) *
    (2 : ℝ) ^ (1 - (Nat.choose k 2 : ℤ))) := by
    unfold muClique
    have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
    have hexp : (-(2 * (Nat.choose k 2 : ℤ) - 1) : ℤ) =
      (-(Nat.choose k 2 : ℤ)) + (1 - (Nat.choose k 2 : ℤ)) := by omega
    rw [hexp, zpow_add₀ h2ne]
    ring

  have hmu_nonneg : (0 : ℝ) ≤ muClique n k := by unfold muClique; positivity

  calc muClique n k
      = muClique n k * 1 := (mul_one _).symm
    _ ≤ muClique n k * ((Nat.choose k 2 : ℝ) * (Nat.choose (n - k) (k - 2) : ℝ) *
        (2 : ℝ) ^ (1 - (Nat.choose k 2 : ℤ))) :=
        mul_le_mul_of_nonneg_left hratio_n hmu_nonneg
    _ = (Nat.choose k 2 : ℝ) * (Nat.choose (n - k) (k - 2) : ℝ) *
        (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(2 * (Nat.choose k 2 : ℤ) - 1)) := hfactor.symm
    _ ≤ deltaClique n k := hge_s2

/-- Eventually $\mu(n, k_0(n) - 3) > 0$, immediate from the asymptotic lower bound. -/
theorem mu_pos_eventually :
    ∀ᶠ (n : ℕ) in atTop, 0 < muClique n (k₀ n - 3) := by
  have h1 := mu_lower_bound 1 one_pos
  have h2 : ∀ᶠ (n : ℕ) in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (h1.and h2).mono
  intro n ⟨hn, hn1⟩
  have hpos : (0 : ℝ) < (↑n : ℝ) ^ ((3 : ℝ) - 1) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  linarith

/-- Asymptotic lower bound $n^{2-\varepsilon} \le \mu^2 / (2\Delta)$ at the shifted
threshold, which is the exponent appearing inside Janson's inequality. -/
theorem mu_sq_over_delta_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      (↑n : ℝ) ^ (2 - ε) ≤
        (muClique n (k₀ n - 3)) ^ 2 / (2 * deltaClique n (k₀ n - 3)) := by
  intro ε hε

  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  have h_delta := delta_mu_sq_bound (ε / 2) hε2
  have h_dge := delta_ge_mu_eventually
  have h_mu := mu_lower_bound 1 one_pos

  have h_large : ∀ᶠ (n : ℕ) in atTop, (2 : ℝ) ≤ (↑n : ℝ) ^ (ε / 2) := by
    have htend := (tendsto_rpow_atTop hε2).comp tendsto_natCast_atTop_atTop
    exact (htend.eventually (eventually_ge_atTop 2)).mono (fun n hn => hn)
  have h_n1 : ∀ᶠ (n : ℕ) in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩

  apply (h_delta.and (h_dge.and (h_mu.and (h_large.and h_n1)))).mono
  intro n ⟨hΔ_upper, hΔ_ge_μ, hμ_lower, h2n, hn1⟩
  set μ := muClique n (k₀ n - 3)
  set Δ := deltaClique n (k₀ n - 3)

  have hn_pos : (0 : ℝ) < (↑n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hμ_pos : (0 : ℝ) < μ := by
    have : (↑n : ℝ) ^ ((3 : ℝ) - 1) ≤ μ := hμ_lower
    calc (0 : ℝ) < (↑n : ℝ) ^ ((3 : ℝ) - 1) := Real.rpow_pos_of_pos hn_pos _
      _ ≤ μ := this
  have hΔ_pos : (0 : ℝ) < Δ := lt_of_lt_of_le hμ_pos hΔ_ge_μ
  have h2Δ_pos : (0 : ℝ) < 2 * Δ := mul_pos two_pos hΔ_pos

  have hμ_sq_pos : (0 : ℝ) < μ ^ 2 := sq_pos_of_pos hμ_pos

  rw [le_div_iff₀ h2Δ_pos]

  calc (↑n : ℝ) ^ (2 - ε) * (2 * Δ)
      ≤ (↑n : ℝ) ^ (2 - ε) * (2 * (μ ^ 2 * (↑n : ℝ) ^ (-2 + ε / 2))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn_pos.le _)
        linarith [hΔ_upper]
    _ = μ ^ 2 * (2 * ((↑n : ℝ) ^ (2 - ε) * (↑n : ℝ) ^ (-2 + ε / 2))) := by ring
    _ = μ ^ 2 * (2 * (↑n : ℝ) ^ (-(ε / 2))) := by
        congr 1; congr 1
        rw [← Real.rpow_add hn_pos]
        congr 1; ring
    _ ≤ μ ^ 2 := by
        have hinv : (↑n : ℝ) ^ (-(ε / 2)) = ((↑n : ℝ) ^ (ε / 2))⁻¹ :=
          Real.rpow_neg hn_pos.le _
        rw [hinv]
        have h_inv_le : 2 * ((↑n : ℝ) ^ (ε / 2))⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ (Real.rpow_pos_of_pos hn_pos _)]
          linarith [h2n]
        calc μ ^ 2 * (2 * ((↑n : ℝ) ^ (ε / 2))⁻¹)
            ≤ μ ^ 2 * 1 := by
              apply mul_le_mul_of_nonneg_left h_inv_le (le_of_lt hμ_sq_pos)
          _ = μ ^ 2 := mul_one _

/-- Sub-Gaussian decay of the $K_{k_0 - 3}$-free probability: for every $\varepsilon > 0$,
$\Pr(G(n,1/2) \text{ is } K_{k_0(n)-3}\text{-free}) \le \exp(-n^{2-\varepsilon})$. -/
theorem cliqueFree_prob_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      probGnHalf n (fun G => G.CliqueFree (k₀ n - 3)) ≤
        Real.exp (-(↑n : ℝ) ^ (2 - ε)) := by
  intro ε hε

  have h_bound := mu_sq_over_delta_bound ε hε
  have h_ge := delta_ge_mu_eventually
  have h_pos := mu_pos_eventually

  have hcombined := h_bound.and (h_ge.and h_pos)
  apply hcombined.mono
  intro n ⟨h_ratio, hge, hpos⟩


  have hjanson := janson_clique_bound n (k₀ n - 3) hpos hge

  calc probGnHalf n (fun G => G.CliqueFree (k₀ n - 3))
      ≤ Real.exp (-(muClique n (k₀ n - 3)) ^ 2 /
          (2 * deltaClique n (k₀ n - 3))) := hjanson
    _ ≤ Real.exp (-(↑n : ℝ) ^ (2 - ε)) := by
        apply Real.exp_le_exp.mpr
        have h2Δ_pos : (0 : ℝ) < 2 * deltaClique n (k₀ n - 3) :=
          mul_pos two_pos (lt_of_lt_of_le hpos hge)
        rw [neg_div, neg_le_neg_iff]
        exact h_ratio

/-- Theorem 8.3.2 (Bollobás 1988), one direction: with very high probability the clique
number of $G(n,1/2)$ is at least $k_0(n) - 3$, the threshold value. The complementary
probability is at most $\exp(-n^{2-\varepsilon})$. -/
theorem clique_number_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      probGnHalf n (fun G => cliqueNum G < k₀ n - 3) ≤
        Real.exp (-(↑n : ℝ) ^ (2 - ε)) := by
  intro ε hε
  have hbound := cliqueFree_prob_bound ε hε
  apply hbound.mono
  intro n hn
  calc probGnHalf n (fun G => cliqueNum G < k₀ n - 3)
      ≤ probGnHalf n (fun G => G.CliqueFree (k₀ n - 3)) := by
        show probGnHalf n (fun G => cliqueNum G < k₀ n - 3) ≤
            probGnHalf n (fun G => G.CliqueFree (k₀ n - 3))
        simp only [probGnHalf]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro G hG
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
        by_cases hk : k₀ n - 3 ≤ n ∧ 0 < k₀ n - 3
        · exact (cliqueNum_lt_iff_cliqueFree G (k₀ n - 3) hk.1 hk.2).mp hG
        · push_neg at hk
          exfalso
          have h0 : k₀ n - 3 = 0 := by have := k₀_le n; omega
          simp [h0] at hG
    _ ≤ Real.exp (-(↑n : ℝ) ^ (2 - ε)) := hn

end ChromaticNumber
