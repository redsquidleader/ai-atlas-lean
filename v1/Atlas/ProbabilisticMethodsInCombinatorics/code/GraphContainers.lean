/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.SimpleGraph
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Finset.Lattice.Fold
set_option maxHeartbeats 800000

open scoped Classical

open SimpleGraph Finset

namespace GraphContainers

variable {V W : Type*}

/-- `IsHFree G H` says that the graph $G$ contains no copy of $H$ as a subgraph. -/
def IsHFree (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  IsEmpty (H.Copy G)

/-- The finset of all $H$-free labelled graphs on the vertex set $\{1, \dots, n\}$. -/
noncomputable def hFreeGraphs (H : SimpleGraph W) (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  @Finset.filter _ (fun G => IsHFree G H) (Classical.decPred _) Finset.univ

/-- The extremal number $\mathrm{ex}(n, H)$: the maximum number of edges in an $H$-free
graph on $n$ vertices. -/
noncomputable def extremalNumber (H : SimpleGraph W) (n : ℕ) : ℕ :=
  (hFreeGraphs H n).sup fun G => G.edgeFinset.card

/-- Theorem 11.2.1 (Graph container theorem, non-bipartite case). For any non-bipartite
graph $H$ and every $\varepsilon > 0$, eventually the number of $H$-free graphs on
$n$ vertices is $2^{(1 \pm \varepsilon) \mathrm{ex}(n, H)}$. -/
theorem count_hFreeGraphs_nonBipartite
    {W : Type*} (H : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (hH : ¬H.IsBipartite) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      (hFreeGraphs H n).card ≤ 2 ^ ⌈((1 + ε) * (extremalNumber H n : ℝ))⌉₊ ∧
      2 ^ ⌊((1 - ε) * (extremalNumber H n : ℝ))⌋₊ ≤ (hFreeGraphs H n).card := by sorry

/-- Conjectured bipartite analogue of the container theorem: for every bipartite $H$ with
a cycle there is a constant $C$ such that the number of $H$-free graphs on $n$ vertices
is at most $2^{C \cdot \mathrm{ex}(n, H)}$. -/
theorem conjecture_hFreeGraphs_bipartite
    {W : Type*} (H : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (hbip : H.IsBipartite) (hcycle : ¬H.IsAcyclic) :
    ∃ C : ℕ, ∀ n : ℕ, (hFreeGraphs H n).card ≤ 2 ^ (C * extremalNumber H n) := by sorry

/-- Erdős–Stone–Simonovits theorem: for a non-bipartite graph $H$,
$\mathrm{ex}(n, H) / \binom{n}{2} \to 1 - 1/(\chi(H) - 1)$ as $n \to \infty$. -/
theorem erdos_stone_simonovits
    {W : Type*} (H : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (hH : ¬H.IsBipartite) :
    Filter.Tendsto (fun n => (extremalNumber H n : ℝ) / (n.choose 2 : ℝ))
      Filter.atTop (nhds (1 - 1 / ((H.chromaticNumber.toNat : ℝ) - 1))) := by sorry

/-- The average degree $2|E(G)| / |V(G)|$ of a finite graph. -/
noncomputable def averageDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

/-- Container algorithm output. Given a graph $G$ with bounded max-to-average-degree
ratio and an independent set $I$, there exist a small fingerprint $\mathrm{fp} \subseteq I$
and an available set such that $I$ is contained in $\mathrm{fp} \cup \mathrm{avail}$, with
quantitative size bounds in terms of $\bar d(G)$. -/
theorem container_algorithm_output
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℝ) (hc : c > 0)
    (hmaxdeg : (G.maxDegree : ℝ) ≤ c * averageDegree G)
    (havgpos : averageDegree G > 0)
    (I : Set V) (hI : G.IsIndepSet I) :
    ∃ (fp avail : Finset V),
      (↑fp : Set V) ⊆ I ∧
      I ⊆ ↑(fp ∪ avail) ∧
      (fp.card : ℝ) ≤ 2 * (1 / (4 * c + 2)) * (Fintype.card V : ℝ) / averageDegree G ∧
      ((fp ∪ avail).card : ℝ) ≤ (1 - 1 / (4 * c + 2)) * (Fintype.card V : ℝ) := by sorry

/-- The container algorithm's available-set output depends only on the fingerprint: two
independent sets producing the same fingerprint yield the same available set. This is the
determinism property needed to encode the algorithm with the fingerprint alone. -/
theorem container_algorithm_deterministic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℝ) (hc : c > 0)
    (hmaxdeg : (G.maxDegree : ℝ) ≤ c * averageDegree G)
    (havgpos : averageDegree G > 0)
    (I I' : Set V) (hI : G.IsIndepSet I) (hI' : G.IsIndepSet I')
    (hfp_eq : (container_algorithm_output G c hc hmaxdeg havgpos I hI).choose =
              (container_algorithm_output G c hc hmaxdeg havgpos I' hI').choose) :
    (container_algorithm_output G c hc hmaxdeg havgpos I hI).choose_spec.choose =
    (container_algorithm_output G c hc hmaxdeg havgpos I' hI').choose_spec.choose := by sorry

/-- Theorem 11.2.3 (Graph container fingerprints). There is $\delta > 0$ such that for
every graph $G$ with bounded max-to-average-degree ratio, every independent set $I$ is
determined by a small fingerprint $S(I) \subseteq I$ together with an available set
$A(S(I))$ depending only on the fingerprint, with $|S(I)| \le 2\delta |V|/\bar d(G)$ and
$|S(I) \cup A(S(I))| \le (1 - \delta)|V|$. -/
theorem graph_container_fingerprints
    (c : ℝ) (hc : c > 0) :
    ∃ δ : ℝ, δ > 0 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.maxDegree : ℝ) ≤ c * averageDegree G →
    averageDegree G > 0 →
    ∃ (S : {I : Set V // G.IsIndepSet I} → Finset V)
      (A : Finset V → Finset V),
    ∀ (I : Set V) (hI : G.IsIndepSet I),
      (↑(S ⟨I, hI⟩) : Set V) ⊆ I ∧
      I ⊆ ↑(S ⟨I, hI⟩) ∪ ↑(A (S ⟨I, hI⟩)) ∧
      ((S ⟨I, hI⟩).card : ℝ) ≤ 2 * δ * (Fintype.card V : ℝ) / averageDegree G ∧
      (((S ⟨I, hI⟩) ∪ (A (S ⟨I, hI⟩))).card : ℝ) ≤ (1 - δ) * (Fintype.card V : ℝ) := by
  classical

  refine ⟨1 / (4 * c + 2), by positivity, ?_⟩
  intro V _ _ G _ hmaxdeg havgpos

  let out := fun (I : Set V) (hI : G.IsIndepSet I) =>
    container_algorithm_output G c hc hmaxdeg havgpos I hI

  let S : {I : Set V // G.IsIndepSet I} → Finset V := fun ⟨I, hI⟩ => (out I hI).choose


  let A : Finset V → Finset V := fun T =>
    if h : ∃ (I : Set V) (hI : G.IsIndepSet I), (out I hI).choose = T
    then (out h.choose h.choose_spec.choose).choose_spec.choose
    else ∅
  refine ⟨S, A, ?_⟩
  intro I hI

  have hprops := (out I hI).choose_spec.choose_spec
  obtain ⟨h1, h2, h3, h4⟩ := hprops

  have hex : ∃ (I' : Set V) (hI' : G.IsIndepSet I'), (out I' hI').choose = (out I hI).choose :=
    ⟨I, hI, rfl⟩
  have hA_is_avail : A (S ⟨I, hI⟩) = (out I hI).choose_spec.choose := by
    show (if h : ∃ (I' : Set V) (hI' : G.IsIndepSet I'), (out I' hI').choose = (out I hI).choose
      then (out h.choose h.choose_spec.choose).choose_spec.choose
      else ∅) = _
    rw [dif_pos hex]
    exact container_algorithm_deterministic G c hc hmaxdeg havgpos
      hex.choose I hex.choose_spec.choose hI hex.choose_spec.choose_spec

  refine ⟨h1, ?_, h3, ?_⟩
  ·
    have : (↑(S ⟨I, hI⟩) : Set V) ∪ ↑(A (S ⟨I, hI⟩)) =
        ↑((out I hI).choose ∪ (out I hI).choose_spec.choose) := by
      simp only [S, Finset.coe_union]
      congr 1
      exact_mod_cast hA_is_avail
    rw [this]; exact h2
  ·
    have : S ⟨I, hI⟩ ∪ A (S ⟨I, hI⟩) =
        (out I hI).choose ∪ (out I hI).choose_spec.choose := by
      show (out I hI).choose ∪ A ((out I hI).choose) = _
      rw [hA_is_avail]
    rw [this]; exact h4

noncomputable section

open MeasureTheory Filter Topology Real

/-- The Erdős–Rényi measure $G(n, p)$ on simple graphs on the vertex set $\{1, \dots, n\}$:
each potential edge is independently present with probability $p$, and the weight of a
graph $G$ is $p^{|E(G)|}(1-p)^{m - |E(G)|}$ with $m = \binom{n}{2}$. -/
def erdosRenyiMeasure (n : ℕ) (p : ℝ) :
    Measure (SimpleGraph (Fin n)) := by
  classical
  let m := (completeGraph (Fin n)).edgeFinset.card
  exact Measure.sum (fun G : SimpleGraph (Fin n) =>
    (ENNReal.ofReal (p ^ G.edgeFinset.card * (1 - p) ^ (m - G.edgeFinset.card))) •
      Measure.dirac G)

/-- The "bad" event in the random graph $G(n, p)$: there exists a triangle-free subgraph
$H \le G$ with more than `threshold` edges. -/
def badEvent (n : ℕ) (threshold : ℝ) : Set (SimpleGraph (Fin n)) := by
  classical
  exact {G | ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.CliqueFree 3 ∧
    (H.edgeFinset.card : ℝ) > threshold}

/-- Container lemma for triangle-free graphs: there is a small collection $\mathcal C$ of
"containers", each with at most $(1/4 + \varepsilon) n^2$ edges, such that every
triangle-free graph on $n$ vertices is a subgraph of some container. -/
theorem triangleFreeContainerLemma
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∃ 𝒞 : Finset (SimpleGraph (Fin n)),
        (𝒞.card : ℝ) ≤ (n : ℝ) ^ (C * (n : ℝ) ^ (3/2 : ℝ)) ∧
        (∀ G ∈ 𝒞, (G.edgeFinset.card : ℝ) ≤ (1/4 + ε) * (n : ℝ)^2) ∧
        (∀ H : SimpleGraph (Fin n), H.CliqueFree 3 → ∃ G ∈ 𝒞, H ≤ G) := by sorry

/-- Chernoff bound for the number of edges of a fixed container intersected with a
$G(n,p)$ sample: with high probability the intersection has at most
$(1/4 + 2\varepsilon) p n^2$ edges. -/
theorem chernoff_erdosRenyi_container
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (p : ℝ),
      0 < p → p ≤ 1 →
      ∀ (C_graph : SimpleGraph (Fin n)),
        (C_graph.edgeFinset.card : ℝ) ≤ (1/4 + ε) * (n : ℝ)^2 →
        erdosRenyiMeasure n p {G | ((C_graph ⊓ G).edgeFinset.card : ℝ) >
          (1/4 + 2*ε) * p * (n : ℝ)^2} ≤
          ENNReal.ofReal (Real.exp (-c * (n : ℝ)^2 * p)) := by sorry

/-- Combining the container cover with the bad event: every realization of the bad event
lies in the union over containers $C$ of the events "$C \cap G$ has too many edges". -/
lemma badEvent_subset_container_union (n : ℕ) (ε : ℝ)
    (𝒞 : Finset (SimpleGraph (Fin n)))
    (hcover : ∀ H : SimpleGraph (Fin n), H.CliqueFree 3 → ∃ G ∈ 𝒞, H ≤ G)
    (p : ℝ) :
    badEvent n ((1/4 + 2*ε) * p * (n : ℝ)^2) ⊆
    ⋃ C ∈ 𝒞, {G : SimpleGraph (Fin n) |
      ((C ⊓ G).edgeFinset.card : ℝ) > (1/4 + 2*ε) * p * (n : ℝ)^2} := by
  intro G hG
  simp only [badEvent, Set.mem_setOf_eq] at hG
  obtain ⟨H, hHG, hHfree, hHedges⟩ := hG
  obtain ⟨C, hCmem, hHC⟩ := hcover H hHfree
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨C, hCmem, ?_⟩
  have hH_inf : H ≤ C ⊓ G := le_inf hHC hHG
  have hcard : H.edgeFinset.card ≤ (C ⊓ G).edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hH_inf)
  linarith [show (H.edgeFinset.card : ℝ) ≤ ((C ⊓ G).edgeFinset.card : ℝ) from by
    exact_mod_cast hcard]

/-- Union bound combined with the container chernoff bound: the probability of the bad
event in $G(n, p)$ is at most $n^{C n^{3/2}} \exp(-c n^2 p)$ for universal constants
$C, c > 0$. -/
theorem unionBound_containerChernoff
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (n : ℕ) (p : ℝ),
      0 < p → p ≤ 1 →
      (erdosRenyiMeasure n p (badEvent n ((1/4 + 2*ε) * p * (n : ℝ)^2))).toReal ≤
        (n : ℝ) ^ (C * (n : ℝ) ^ (3/2 : ℝ)) * Real.exp (-c * (n : ℝ)^2 * p) := by
  obtain ⟨C, hC, hcontainer⟩ := triangleFreeContainerLemma ε hε
  obtain ⟨c, hc, hchernoff⟩ := chernoff_erdosRenyi_container ε hε
  refine ⟨C, c, hC, hc, ?_⟩
  intro n p hp hp1
  obtain ⟨𝒞, hcard, hedges, hcover⟩ := hcontainer n

  have hfinal_ennreal :
      erdosRenyiMeasure n p (badEvent n ((1/4 + 2*ε) * p * (n : ℝ)^2)) ≤
      ∑ C_graph ∈ 𝒞, erdosRenyiMeasure n p
        {G | ((C_graph ⊓ G).edgeFinset.card : ℝ) > (1/4 + 2*ε) * p * (n : ℝ)^2} :=
    le_trans (MeasureTheory.measure_mono (badEvent_subset_container_union n ε 𝒞 hcover p))
      (measure_biUnion_finset_le 𝒞 _)

  have hsum_bound :
      ∑ C_graph ∈ 𝒞, erdosRenyiMeasure n p
        {G | ((C_graph ⊓ G).edgeFinset.card : ℝ) > (1/4 + 2*ε) * p * (n : ℝ)^2} ≤
      𝒞.card • ENNReal.ofReal (Real.exp (-c * (n : ℝ)^2 * p)) :=
    Finset.sum_le_card_nsmul _ _ _
      (fun C_graph hC_mem => hchernoff n p hp hp1 C_graph (hedges C_graph hC_mem))

  have hbound_ne_top :
      𝒞.card • ENNReal.ofReal (Real.exp (-c * (n : ℝ)^2 * p)) ≠ ⊤ := by
    induction 𝒞.card with
    | zero => simp
    | succ k _ =>
      rw [succ_nsmul]
      exact ENNReal.add_ne_top.mpr ⟨by assumption, ENNReal.ofReal_ne_top⟩

  have hreal :
      (erdosRenyiMeasure n p (badEvent n ((1/4 + 2*ε) * p * (n : ℝ)^2))).toReal ≤
      (𝒞.card : ℝ) * Real.exp (-c * (n : ℝ)^2 * p) := by
    have h1 := ENNReal.toReal_mono hbound_ne_top (le_trans hfinal_ennreal hsum_bound)
    rw [ENNReal.toReal_nsmul, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] at h1
    simpa [nsmul_eq_mul] using h1

  calc (erdosRenyiMeasure n p (badEvent n ((1/4 + 2*ε) * p * (n : ℝ)^2))).toReal
      ≤ (𝒞.card : ℝ) * Real.exp (-c * (n : ℝ)^2 * p) := hreal
    _ ≤ (n : ℝ) ^ (C * (n : ℝ) ^ (3/2 : ℝ)) * Real.exp (-c * (n : ℝ)^2 * p) :=
        mul_le_mul_of_nonneg_right hcard (le_of_lt (Real.exp_pos _))

/-- Pointwise inequality used in the asymptotic analysis: when $p_n n^{1/2}/\log n$ is
large enough, the expression $C n^{3/2} \log n - c n^2 p_n$ is bounded above by any
prescribed $b$. -/
lemma asymptotic_bound_pointwise
    (C c b : ℝ) (hc : 0 < c) (n : ℕ) (pn : ℝ) (hn2 : 2 < n)
    (hn : (C + 1) / c ≤ pn * (n : ℝ) ^ (1/2 : ℝ) / Real.log ↑n)
    (hlarge : -(n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n ≤ b) :
    C * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n - c * (n : ℝ) ^ 2 * pn ≤ b := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hnn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast show 1 < n by omega
  have hlogn : 0 < Real.log ↑n := Real.log_pos hnn
  have hn32 : 0 < (n : ℝ) ^ (3/2 : ℝ) := rpow_pos_of_pos hn0 _
  have step1 : (C + 1) * Real.log ↑n ≤ c * (pn * (n : ℝ) ^ (1/2 : ℝ)) := by
    rw [div_le_div_iff₀ hc hlogn] at hn; linarith
  have step2 : (C + 1) * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n ≤ c * pn * (n : ℝ) ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_right step1 hn32.le
    have rpow_eq : (n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ (3/2 : ℝ) = (n : ℝ) ^ (2 : ℕ) := by
      rw [← rpow_add hn0, show (1:ℝ)/2 + 3/2 = (2 : ℕ) from by norm_num, rpow_natCast]
    calc (C + 1) * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n
        = (C + 1) * Real.log ↑n * (n : ℝ) ^ (3/2 : ℝ) := by ring
      _ ≤ c * (pn * (n : ℝ) ^ (1/2 : ℝ)) * (n : ℝ) ^ (3/2 : ℝ) := h2
      _ = c * pn * ((n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ (3/2 : ℝ)) := by ring
      _ = c * pn * (n : ℝ) ^ 2 := by rw [rpow_eq]
  linarith [step2, hlarge]

/-- If $p_n \cdot n^{1/2} / \log n \to \infty$, then the exponent
$C n^{3/2} \log n - c n^2 p_n$ tends to $-\infty$. -/
lemma exponent_tends_to_neg_inf (C c : ℝ) (_hC : 0 < C) (hc : 0 < c)
    (p : ℕ → ℝ) (hp_growth : Tendsto (fun n : ℕ => p n * (n : ℝ) ^ (1/2 : ℝ) / Real.log ↑n) atTop atTop) :
    Tendsto (fun n : ℕ => C * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n - c * (n : ℝ) ^ 2 * p n) atTop atBot := by
  rw [tendsto_atBot]; intro b; rw [tendsto_atTop] at hp_growth
  obtain ⟨N1, hN1⟩ := (hp_growth ((C + 1) / c)).exists_forall_of_atTop
  have hN2 : ∃ N2 : ℕ, ∀ n : ℕ, N2 ≤ n → -(n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n ≤ b := by
    by_cases hb : 0 ≤ b
    · exact ⟨3, fun n hn => by
        have : 0 ≤ (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n :=
          mul_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)
            (le_of_lt (Real.log_pos (by exact_mod_cast show 1 < n by omega)))
        linarith⟩
    · push Not at hb
      refine ⟨max 3 (Nat.ceil (-b) + 1), fun n hn => ?_⟩
      have hn3 : 3 ≤ n := le_of_max_le_left hn
      have hn_ceil : Nat.ceil (-b) + 1 ≤ n := le_of_max_le_right hn
      have hn0 : (0 : ℝ) < n := by positivity
      have hnn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast show 1 < n by omega
      have h_rpow_ge : (n : ℝ) ≤ (n : ℝ) ^ (3/2 : ℝ) := by
        conv_lhs => rw [show (n : ℝ) = (n : ℝ) ^ (1 : ℝ) from (rpow_one _).symm]
        exact rpow_le_rpow_of_exponent_le (le_of_lt hnn) (by norm_num : (1 : ℝ) ≤ 3/2)
      have h_log_ge : (1 : ℝ) ≤ Real.log ↑n := by
        have : Real.exp 1 ≤ (n : ℝ) := le_of_lt (calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          _ < 3 := by norm_num
          _ ≤ (n : ℝ) := by exact_mod_cast hn3)
        rwa [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < ↑n)]
      linarith [show -b < (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n from calc
        -b ≤ Nat.ceil (-b) := Nat.le_ceil (-b)
        _ < Nat.ceil (-b) + 1 := by linarith
        _ ≤ (n : ℝ) := by exact_mod_cast hn_ceil
        _ ≤ (n : ℝ) ^ (3/2 : ℝ) := h_rpow_ge
        _ = (n : ℝ) ^ (3/2 : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n :=
            mul_le_mul_of_nonneg_left h_log_ge (rpow_nonneg (Nat.cast_nonneg n) _)]
  obtain ⟨N2, hN2⟩ := hN2
  filter_upwards [Ioi_mem_atTop (max (max N1 N2) 2)] with n hn
  exact asymptotic_bound_pointwise C c b hc n (p n)
    (by have := Set.mem_Ioi.mp hn; omega) (hN1 n (by have := Set.mem_Ioi.mp hn; omega))
    (hN2 n (by have := Set.mem_Ioi.mp hn; omega))

/-- Mantel-in-random-graphs corollary: if $p_n n^{1/2}/\log n \to \infty$, then with
probability tending to $1$ every triangle-free subgraph of $G(n, p_n)$ has at most
$(1/4 + 2\varepsilon) p_n n^2$ edges. -/
theorem mantel_in_random_graphs
    (p : ℕ → ℝ) (hp_pos : ∀ᶠ n in atTop, 0 < p n) (hp_le : ∀ᶠ n in atTop, p n ≤ 1)
    (hp_growth : Tendsto (fun n => p n * (n : ℝ) ^ (1/2 : ℝ) / Real.log n) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (erdosRenyiMeasure n (p n)
      (badEvent n ((1/4 + 2*ε) * p n * (n : ℝ)^2))).toReal) atTop (nhds 0) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := unionBound_containerChernoff ε hε
  have hexp_to_zero : Tendsto
      (fun n : ℕ => Real.exp (C * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n - c * (n : ℝ) ^ 2 * p n))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (exponent_tends_to_neg_inf C c hC hc p hp_growth)
  have hprod_eq : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (C * (n : ℝ) ^ (3/2 : ℝ)) * Real.exp (-c * (n : ℝ)^2 * p n) =
      Real.exp (C * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n - c * (n : ℝ) ^ 2 * p n) := by
    filter_upwards [Ioi_mem_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Set.mem_Ioi.mp hn
    rw [show (n : ℝ) ^ (C * (n : ℝ) ^ (3/2 : ℝ)) =
        Real.exp (C * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n) from by
      rw [rpow_def_of_pos hn0, mul_comm], ← Real.exp_add, sub_eq_add_neg]
    congr 1; ring
  exact squeeze_zero'
    (.of_forall (fun n => ENNReal.toReal_nonneg))
    (by filter_upwards [hp_pos, hp_le] with n hpn hpn1; exact hbound n (p n) hpn hpn1)
    (hexp_to_zero.congr' (hprod_eq.mono (fun n hn => hn.symm)))

end

end GraphContainers
