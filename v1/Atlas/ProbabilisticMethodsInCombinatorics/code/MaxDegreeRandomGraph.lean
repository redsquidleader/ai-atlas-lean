/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Order.UpperLower.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter7.MaxDegree

set_option maxHeartbeats 800000
set_option maxRecDepth 1000

open Finset Filter
open scoped Classical

namespace MaxDegreeRandomGraph

/-- The number of labeled simple graphs on $\{1, \dots, n\}$ whose maximum degree is at
most $\lfloor n/2 \rfloor$. -/
noncomputable def numGraphsMaxDegBounded (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
    G.maxDegree ≤ n / 2))

/-- Total number of labeled simple graphs on $n$ vertices, equal to $2^{\binom{n}{2}}$. -/
noncomputable def numGraphsTotal (n : ℕ) : ℕ :=
  Fintype.card (SimpleGraph (Fin n))

/-- Probability that the uniform random labeled graph $G(n, 1/2)$ has maximum degree at most
$\lfloor n/2 \rfloor$. -/
noncomputable def probMaxDegAtMostHalf (n : ℕ) : ℝ :=
  (numGraphsMaxDegBounded n : ℝ) / (numGraphsTotal n : ℝ)

end MaxDegreeRandomGraph

/-- Theorem 7.2.5 (Riordan-Selby 2000). The probability that the random graph $G(n, 1/2)$
has maximum degree at most $\lfloor n/2 \rfloor$ satisfies
$\mathbb{P}^{1/n} \to c$ for some constant $c \in (1/2, 1)$, where $c$ is the
exponential of the supremum of the explicit functional $g$ defined on the normal-labels model. -/
theorem riordan_selby_maxdeg :
  let c := Real.exp (sSup (Set.range MaxDegreeNormalLabels.g))
  (1/2 : ℝ) < c ∧ c < 1 ∧
    Tendsto (fun n : ℕ => (MaxDegreeRandomGraph.probMaxDegAtMostHalf n) ^ ((1 : ℝ) / (n : ℝ)))
      atTop (nhds c) := by sorry

/-- Proposition 7.2.6 (max degree with normal labels). In the surrogate model where
vertices receive i.i.d. normal labels and an edge is kept if both endpoints have nonpositive
labels, the probability of "all labels nonpositive" raised to the power $1/n$ converges to
some constant $c \in (1/2, 1)$. -/
theorem normal_model_maxdeg :
  ∃ c : ℝ, (1/2 : ℝ) < c ∧ c < 1 ∧
    Tendsto (fun n : ℕ => (MaxDegreeNormalLabels.prob_all_nonpos n) ^ ((1 : ℝ) / (n : ℝ)))
      atTop (nhds c) := by sorry
