/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TaftHopfInstance
import Atlas.TensorCategories.code.QBinomial

open Coalgebra HopfAlgebra
open scoped TensorProduct

namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

set_option linter.unusedSectionVars false in
/-- If `q` is a primitive `n`th root of unity and `b * a = q⁻¹ · (a * b)` in a `k`-algebra, with
both `a^n` and `b^n` vanishing, then `(a + b)^n = 0` by the `q`-binomial expansion. -/
theorem q_comm_sum_pow_zero {B : Type*} [Ring B] [Algebra k B]
    (hn : 1 < n) (hq : IsPrimitiveRoot q n)
    (a b : B) (hcomm : b * a = algebraMap k B q⁻¹ * (a * b))
    (ha : a ^ n = 0) (hb : b ^ n = 0) :
    (a + b) ^ n = 0 := by
  have hqi : IsPrimitiveRoot q⁻¹ n := hq.inv
  rw [q_comm_power q⁻¹ n hn hqi a b hcomm, ha, hb, add_zero]

end TaftAlgebraType
