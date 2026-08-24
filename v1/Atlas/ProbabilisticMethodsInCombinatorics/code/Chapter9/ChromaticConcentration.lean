/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring
set_option maxHeartbeats 400000

open MeasureTheory Measure SimpleGraph Real

namespace ChromaticConcentration

/-- Two graphs $G$ and $G'$ on vertex set $V$ differ only at vertex $v$: their adjacency
relations agree on all pairs not involving $v$. -/
def DiffOnlyAt {V : Type*} (G G' : SimpleGraph V) (v : V) : Prop :=
  ∀ a b, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)

/-- Symmetry of `DiffOnlyAt`: if $G$ and $G'$ differ only at $v$, so do $G'$ and $G$. -/
lemma DiffOnlyAt.symm {V : Type*} {G G' : SimpleGraph V} {v : V}
    (h : DiffOnlyAt G G' v) : DiffOnlyAt G' G v :=
  fun a b ha hb => (h a b ha hb).symm

/-- The chromatic number of a graph on `Fin n`, viewed as a real number. -/
noncomputable def chromaticNumberReal (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  (G.chromaticNumber.toNat : ℝ)


/-- Upper-tail bounded differences inequality applied to the chromatic number of $G(n,p)$:
$\mathbb{P}(\chi(G) - \mathbb{E}\chi(G) \geq \varepsilon) \leq \exp(-2\varepsilon^2/(n-1))$. -/
theorem bdi_upper_tail (n : ℕ) (hn : 2 ≤ n) (p : ↑unitInterval) (ε : ℝ) (hε : 0 ≤ ε) :
    (SimpleGraph.binomialRandom (Fin n) p).real
      {G | ε ≤ chromaticNumberReal n G -
        ∫ G', chromaticNumberReal n G' ∂SimpleGraph.binomialRandom (Fin n) p}
      ≤ Real.exp (-2 * ε ^ 2 / (↑(n - 1) : ℝ)) := by sorry


/-- Lower-tail bounded differences inequality applied to the chromatic number of $G(n,p)$:
$\mathbb{P}(\mathbb{E}\chi(G) - \chi(G) \geq \varepsilon) \leq \exp(-2\varepsilon^2/(n-1))$. -/
theorem bdi_lower_tail (n : ℕ) (hn : 2 ≤ n) (p : ↑unitInterval) (ε : ℝ) (hε : 0 ≤ ε) :
    (SimpleGraph.binomialRandom (Fin n) p).real
      {G | ε ≤ ∫ G', chromaticNumberReal n G' ∂SimpleGraph.binomialRandom (Fin n) p -
        chromaticNumberReal n G}
      ≤ Real.exp (-2 * ε ^ 2 / (↑(n - 1) : ℝ)) := by sorry

/-- Shamir-Spencer concentration of the chromatic number (Theorem 9.3.1, 1987):
$\mathbb{P}(|\chi(G(n,p)) - \mathbb{E}\chi(G(n,p))| \geq \lambda\sqrt{n-1}) \leq 2e^{-2\lambda^2}$. -/
theorem shamir_spencer (n : ℕ) (hn : 2 ≤ n) (p : ↑unitInterval) (l : ℝ) (hl : 0 ≤ l) :
    (SimpleGraph.binomialRandom (Fin n) p).real
      {G | l * Real.sqrt (↑(n - 1) : ℝ) ≤
        |chromaticNumberReal n G -
          ∫ G', chromaticNumberReal n G' ∂SimpleGraph.binomialRandom (Fin n) p|}
      ≤ 2 * Real.exp (-2 * l ^ 2) := by
  set μ := SimpleGraph.binomialRandom (Fin n) p
  set EZ := ∫ G', chromaticNumberReal n G' ∂μ
  set t := l * Real.sqrt (↑(n - 1) : ℝ)

  have hsub : {G | t ≤ |chromaticNumberReal n G - EZ|} ⊆
      {G | t ≤ chromaticNumberReal n G - EZ} ∪ {G | t ≤ EZ - chromaticNumberReal n G} := by
    intro G hG
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_cases h : 0 ≤ chromaticNumberReal n G - EZ
    · left; linarith [abs_of_nonneg h]
    · right; push Not at h; linarith [abs_of_neg h]
  have ht : 0 ≤ t := mul_nonneg hl (Real.sqrt_nonneg _)
  have hn1_pos : (0 : ℝ) < (↑(n - 1) : ℝ) := Nat.cast_pos.mpr (by omega)

  calc μ.real {G | t ≤ |chromaticNumberReal n G - EZ|}
      ≤ μ.real ({G | t ≤ chromaticNumberReal n G - EZ} ∪
                {G | t ≤ EZ - chromaticNumberReal n G}) :=
        measureReal_mono hsub
    _ ≤ μ.real {G | t ≤ chromaticNumberReal n G - EZ} +
        μ.real {G | t ≤ EZ - chromaticNumberReal n G} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-2 * t ^ 2 / (↑(n - 1) : ℝ)) +
        Real.exp (-2 * t ^ 2 / (↑(n - 1) : ℝ)) :=
        add_le_add (bdi_upper_tail n hn p t ht) (bdi_lower_tail n hn p t ht)
    _ = 2 * Real.exp (-2 * l ^ 2) := by

        rw [← two_mul]
        congr 1
        rw [show t = l * Real.sqrt (↑(n - 1) : ℝ) from rfl]
        rw [mul_pow, Real.sq_sqrt (le_of_lt hn1_pos)]
        field_simp

end ChromaticConcentration
