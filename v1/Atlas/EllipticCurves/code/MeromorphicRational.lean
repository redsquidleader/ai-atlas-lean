/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Polynomial

/-- Every meromorphic function on the Riemann sphere (i.e., a function on `ℂ` that is meromorphic
both on `ℂ` and at infinity via `f ∘ Inv.inv` at `0`) is rational: there exist polynomials `p` and
`q` with `q ≠ 0` such that `f z = p.eval z / q.eval z` away from the roots of `q`. -/
theorem meromorphic_on_sphere_is_rational
    (f : ℂ → ℂ) (hf : Meromorphic f)
    (hf_inf : MeromorphicAt (f ∘ Inv.inv) 0) :
    ∃ (p q : Polynomial ℂ), q ≠ 0 ∧
      ∀ z, ¬q.IsRoot z → f z = p.eval z / q.eval z := by sorry
