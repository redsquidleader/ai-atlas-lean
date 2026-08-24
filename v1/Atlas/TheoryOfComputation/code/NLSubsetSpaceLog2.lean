/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.LogSpace
import Atlas.TheoryOfComputation.code.SpaceComplexity

open SpaceComplexity LogSpace

namespace LogSpace

/--
**Savitch's theorem at the log-space level.** If a language `A` is decidable by
a nondeterministic TM in space `O(log n)`, then it is decidable by a
deterministic TM in space `O((log n)²)`. This is the instance of Savitch's
theorem `NSPACE(f) ⊆ SPACE(f²)` with `f(n) = log n`, used to derive
`NL ⊆ SPACE(log² n)`.
-/
theorem savitch_log
    {Γ : Type} (A : Set (List Γ)) (hA : InNSPACE log A) :
    InSPACE (fun n => (log n) ^ 2) A := by
  obtain ⟨Q, hFin, hDec, N, hLang, g, hAsymp, hSpace⟩ := hA
  haveI := hFin
  haveI := hDec
  have hLang_cond : ∀ w ∈ N.language, ∀ s ∈ w, s ∈ N.inputAlpha := by
    intro w hw s hs
    exact hw.1 s hs
  obtain ⟨Q', hFin', hDec', M, hMLang, g', hg'bound, hMSpace⟩ :=
    SpaceComplexity.dtm_of_nspace_bounded N g hSpace hLang_cond
  refine ⟨Q', hFin', hDec', M, ?_, g', ?_, hMSpace⟩
  · exact hMLang.trans hLang
  · obtain ⟨c, n₀, hc, hbnd⟩ := hAsymp
    refine ⟨c ^ 2, n₀, by positivity, fun n hn => ?_⟩
    calc g' n ≤ (g n) ^ 2 := hg'bound n
      _ ≤ (c * log n) ^ 2 := Nat.pow_le_pow_left (hbnd n hn) 2
      _ = c ^ 2 * (log n) ^ 2 := Nat.mul_pow c (log n) 2

/--
**`NL ⊆ SPACE(log² n)`.** Every language decidable in nondeterministic
logarithmic space is decidable in `O((log n)²)` deterministic space. Immediate
consequence of `savitch_log` applied to the definition `InNL A := InNSPACE log A`.
-/
theorem nl_subset_space_log2 {Γ : Type} (A : Set (List Γ)) :
    InNL A → InSPACE (fun n => (log n) ^ 2) A := by
  intro hA
  unfold InNL at hA
  exact savitch_log A hA

end LogSpace
