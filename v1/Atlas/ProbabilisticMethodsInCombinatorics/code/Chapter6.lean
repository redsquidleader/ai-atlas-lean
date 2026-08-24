/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.Basic

set_option maxHeartbeats 400000

namespace LovaszLocalLemma

open Set Finset

/-- The coloring $c : \mathbb{R} \to \text{Fin}\ k$ is multicolored on the set $T$ if every color $i \in \text{Fin}\ k$ is attained by some $x \in T$. -/
def IsMulticolored (k : ℕ) (c : ℝ → Fin k) (T : Set ℝ) : Prop :=
  ∀ i : Fin k, ∃ x ∈ T, c x = i

/-- The translate of $S \subseteq \mathbb{R}$ by $t$, i.e. $S + t = \{s + t : s \in S\}$. -/
def translate (S : Set ℝ) (t : ℝ) : Set ℝ := (· + t) '' S

/-- The set of $k$-colorings of $\mathbb{R}$ that are multicolored on the translate $S + t$. -/
def goodColorings (k : ℕ) (S : Finset ℝ) (t : ℝ) : Set (ℝ → Fin k) :=
  {c | IsMulticolored k c (translate (↑S) t)}

/-- The evaluation event $\{c : \mathbb{R} \to \text{Fin}\ k \mid c(x) = i\}$ is clopen in the product topology with discrete fibres. -/
lemma isClopen_eval_eq {k : ℕ} (x : ℝ) (i : Fin k) :
    IsClopen {c : ℝ → Fin k | c x = i} := by
  have heq : {c : ℝ → Fin k | c x = i} = (fun c => c x) ⁻¹' {i} := by
    ext c; simp
  rw [heq]
  exact ⟨(isClosed_discrete _).preimage (continuous_apply x),
         (isOpen_discrete _).preimage (continuous_apply x)⟩

/-- For $k \ge 1$, the set of colorings that are multicolored on $S + t$ is closed in the product topology. -/
lemma isClosed_goodColorings {k : ℕ} (_hk : 0 < k) (S : Finset ℝ) (t : ℝ) :
    IsClosed (goodColorings k S t) := by
  suffices h : goodColorings k S t =
      ⋂ (i : Fin k), ⋃ s ∈ S, {c : ℝ → Fin k | c (↑s + t) = i} by
    rw [h]
    apply isClosed_iInter
    intro i
    exact S.finite_toSet.isClosed_biUnion (fun s _ =>
      (isClopen_eval_eq (↑s + t) i).1)
  ext c
  simp only [goodColorings, IsMulticolored, translate, Set.mem_setOf_eq, Set.mem_image,
    Set.mem_iInter, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · intro h i
    obtain ⟨x, ⟨s, hs, hsx⟩, hc⟩ := h i
    exact ⟨s, hs, hsx ▸ hc⟩
  · intro h i
    obtain ⟨s, hs, hc⟩ := h i
    exact ⟨s + t, ⟨s, hs, rfl⟩, hc⟩

/-- Finite-translate version (proved via the symmetric LLL): under the size condition $e \cdot (m(m-1) + 1) \cdot k \cdot (1 - 1/k)^m \le 1$, for any finite set of shifts $T$ there is a $k$-coloring of $\mathbb{R}$ that is multicolored on every translate $S + t$, $t \in T$. -/
theorem lll_finite_coloring {m k : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    (S : Finset ℝ) (hS : S.card = m)
    (hcond : Real.exp 1 * ((m * (m - 1) + 1 : ℕ) : ℝ) * (k : ℝ) *
      (1 - 1 / (k : ℝ)) ^ m ≤ 1)
    (T : Finset ℝ) :
    ∃ c : ℝ → Fin k, ∀ t ∈ T,
      IsMulticolored k c (translate (↑S) t) := by sorry

/-- Erdős–Lovász multicolor theorem: under the same size condition, by compactness one obtains a single coloring of $\mathbb{R}$ that is multicolored on every translate $S + t$ for $t \in \mathbb{R}$. -/
theorem erdos_lovasz_multicolor {m : ℕ} {k : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    (S : Finset ℝ) (hS : S.card = m)
    (hcond : Real.exp 1 * ((m * (m - 1) + 1 : ℕ) : ℝ) * (k : ℝ) *
      (1 - 1 / (k : ℝ)) ^ m ≤ 1) :
    ∃ c : ℝ → Fin k, ∀ t : ℝ, IsMulticolored k c (translate (↑S) t) := by
  classical
  have hk_pos : (0 : ℕ) < k := by omega
  have hfin : ∀ (u : Finset ℝ),
      (Set.univ ∩ ⋂ t ∈ u, goodColorings k S t).Nonempty := by
    intro u
    obtain ⟨c, hc⟩ := lll_finite_coloring hk hm S hS hcond u
    exact ⟨c, Set.mem_inter trivial (Set.mem_biInter (fun t ht => hc t ht))⟩
  have hcompact : IsCompact (Set.univ : Set (ℝ → Fin k)) := isCompact_univ
  have hclosed : ∀ t : ℝ, IsClosed (goodColorings k S t) :=
    fun t => isClosed_goodColorings hk_pos S t
  have key := hcompact.inter_iInter_nonempty
    (fun t : ℝ => goodColorings k S t)
    (fun t => hclosed t)
    (fun u => hfin u)
  obtain ⟨c, _, hc⟩ := key
  exact ⟨c, fun t => Set.mem_iInter.mp hc t⟩

end LovaszLocalLemma

noncomputable section

namespace Beck

open Set Topology Finset

/-- The arithmetic progression $a, a+d, \dots, a+(k-1)d$ is monochromatic under the $\{0,1\}$-coloring $c$ of $\mathbb{Z}$ if all of its $k$ terms have the same color as $a$. -/
def IsMonochromaticAP (c : ℤ → Bool) (k : ℕ) (a d : ℤ) : Prop :=
  ∀ i : Fin k, c (a + ↑(i : ℕ) * d) = c a

/-- The set of colorings under which a fixed AP $(a, d, k)$ is monochromatic is open in the product topology with discrete fibres. -/
lemma isOpen_monochromaticAP (k : ℕ) (a d : ℤ) :
    IsOpen {c : ℤ → Bool | IsMonochromaticAP c k a d} := by
  simp only [IsMonochromaticAP, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  have h : {c : ℤ → Bool | c (a + ↑(i : ℕ) * d) = c a} =
    (fun c => (c (a + ↑(i : ℕ) * d), c a)) ⁻¹' {p : Bool × Bool | p.1 = p.2} := by
    ext c; simp
  rw [h]
  exact ((continuous_apply _).prodMk (continuous_apply _)).isOpen_preimage _ (isOpen_discrete _)

/-- Finite version of Beck's theorem on monochromatic APs: for any $\varepsilon > 0$ there is a threshold $k_0$ such that any finite list of AP constraints $(k, a, d)$ with $k \ge k_0$ and $0 < d < 2^{(1-\varepsilon) k}$ can be simultaneously broken by some $\{0,1\}$-coloring of $\mathbb{Z}$. -/
theorem finite_consistency (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ (n : ℕ) (constraints : Fin n → ℕ × ℤ × ℤ),
      (∀ i, k₀ ≤ (constraints i).1 ∧ (0 : ℤ) < (constraints i).2.2 ∧
        ((constraints i).2.2 : ℝ) < (2 : ℝ) ^ ((1 - ε) * ((constraints i).1 : ℝ))) →
      ∃ c : ℤ → Bool, ∀ i, ¬IsMonochromaticAP c (constraints i).1
        (constraints i).2.1 (constraints i).2.2 := by sorry

/-- Beck's theorem (via compactness): for any $\varepsilon > 0$ there exist a threshold $k_0$ and a $\{0,1\}$-coloring $c$ of $\mathbb{Z}$ such that no arithmetic progression of length $k \ge k_0$ with common difference $0 < d < 2^{(1-\varepsilon) k}$ is monochromatic under $c$. -/
theorem beck_coloring_ap (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∃ c : ℤ → Bool, ∀ k : ℕ, k₀ ≤ k → ∀ a d : ℤ,
      0 < d → (d : ℝ) < (2 : ℝ) ^ ((1 - ε) * (k : ℝ)) →
      ¬ IsMonochromaticAP c k a d := by
  classical
  obtain ⟨k₀, hk₀⟩ := finite_consistency ε hε
  refine ⟨k₀, ?_⟩
  by_contra h_all_bad
  push Not at h_all_bad
  have h_cover : (Set.univ : Set (ℤ → Bool)) ⊆
      ⋃ (p : ℕ × ℤ × ℤ), if k₀ ≤ p.1 ∧ (0 : ℤ) < p.2.2 ∧
        (p.2.2 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.1 : ℝ))
        then {c | IsMonochromaticAP c p.1 p.2.1 p.2.2} else ∅ := by
    intro c _
    obtain ⟨k, hk, a, d, hd_pos, hd_bound, h_mono⟩ := h_all_bad c
    simp only [Set.mem_iUnion]
    exact ⟨(k, a, d), by simp [hk, hd_pos, hd_bound, h_mono]⟩
  have h_open : ∀ (p : ℕ × ℤ × ℤ), IsOpen
      (if k₀ ≤ p.1 ∧ (0 : ℤ) < p.2.2 ∧ (p.2.2 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.1 : ℝ))
        then {c : ℤ → Bool | IsMonochromaticAP c p.1 p.2.1 p.2.2} else ∅) := by
    intro ⟨k, a, d⟩
    split_ifs
    · exact isOpen_monochromaticAP k a d
    · exact isOpen_empty
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ h_open h_cover
  set t' := t.filter (fun p => k₀ ≤ p.1 ∧ (0 : ℤ) < p.2.2 ∧
    (p.2.2 : ℝ) < (2 : ℝ) ^ ((1 - ε) * (p.1 : ℝ))) with ht'_def
  set constraints : Fin t'.card → ℕ × ℤ × ℤ := fun i => ((t'.equivFin.symm i) : ℕ × ℤ × ℤ)
  have h_valid : ∀ i, k₀ ≤ (constraints i).1 ∧ (0 : ℤ) < (constraints i).2.2 ∧
      ((constraints i).2.2 : ℝ) < (2 : ℝ) ^ ((1 - ε) * ((constraints i).1 : ℝ)) := by
    intro i
    have := ((t'.equivFin.symm i) : {x // x ∈ t'}).2
    simp only [ht'_def, Finset.mem_filter] at this
    exact this.2
  obtain ⟨c, hc⟩ := hk₀ t'.card constraints h_valid
  have hc_cover := ht (Set.mem_univ c)
  rw [Set.mem_iUnion₂] at hc_cover
  obtain ⟨p, hp_mem, hcp⟩ := hc_cover
  split_ifs at hcp with hp_valid
  · have hp_t' : p ∈ t' := Finset.mem_filter.mpr ⟨hp_mem, hp_valid⟩
    have ⟨i, hi⟩ : ∃ i : Fin t'.card, constraints i = p :=
      ⟨t'.equivFin ⟨p, hp_t'⟩, by simp [constraints]⟩
    exact (hc i) (hi ▸ hcp)
  · exact absurd hcp (Set.notMem_empty _)

end Beck
