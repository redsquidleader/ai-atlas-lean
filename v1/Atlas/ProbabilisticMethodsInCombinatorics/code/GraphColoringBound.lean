/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

namespace GraphColoringBound


/-- Theorem 10.4.15 (Sah–Sawhney–Stoner–Zhao 2020). For every $d$-regular graph $G$ on
$n$ vertices and every $q \ge 1$, the number $c_q(G)$ of proper $q$-colourings satisfies
$c_q(G) \le c_q(K_{d,d})^{n/(2d)}$. -/
theorem sah_sawhney_colorings_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (q : ℕ) :
    (Nat.card (G.Coloring (Fin q)) : ℝ) ≤
      (Nat.card ((completeBipartiteGraph (Fin d) (Fin d)).Coloring (Fin q)) : ℝ) ^
        ((Fintype.card V : ℝ) / (2 * (d : ℝ))) := by sorry

end GraphColoringBound
