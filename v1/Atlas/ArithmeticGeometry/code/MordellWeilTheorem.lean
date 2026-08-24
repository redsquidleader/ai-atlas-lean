/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Heights

noncomputable section

namespace EllipticCurve.MordellWeil

open EllipticCurve.WeakMordellWeil CanonicalHeight

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]

/-- Existence of the canonical (Néron-Tate) height on an elliptic curve over $\mathbb{Q}$: a function $\hat{h}$ that is nonnegative, satisfies $\hat{h}(2P) = 4\hat{h}(P)$, the parallelogram law $\hat{h}(P+Q) + \hat{h}(P-Q) = 2\hat{h}(P) + 2\hat{h}(Q)$, and the Northcott property (sublevel sets are finite). -/
theorem canonical_height_exists :
    ∃ (ĥ : W.toAffine.Point → ℝ),
      (∀ P, 0 ≤ ĥ P) ∧
      (∀ P, ĥ ((2 : ℤ) • P) = 4 * ĥ P) ∧
      (∀ P Q, ĥ (P + Q) + ĥ (P - Q) = 2 * ĥ P + 2 * ĥ Q) ∧
      (∀ B : ℝ, {P | ĥ P ≤ B}.Finite) := by sorry

/-- Mordell-Weil theorem (special case): the group $E(\mathbb{Q})$ of an elliptic curve over $\mathbb{Q}$ admitting a 2-isogeny is finitely generated. -/
theorem mordell_weil_special
    (data : TwoIsogenyData W) :
    AddGroup.FG W.toAffine.Point := by
  obtain ⟨ĥ, h_nonneg, h_double, h_par, h_northcott⟩ := canonical_height_exists W
  exact addGroup_fg_of_height_descent ĥ h_nonneg h_double h_par
    (corollary_25_7' W data) h_northcott

/-- (Theorem 25.23, Mordell-Weil) Restatement: $E(\mathbb{Q})$ is finitely generated when there is a 2-isogeny. -/
theorem theorem_25_23 (data : TwoIsogenyData W) :
    AddGroup.FG W.toAffine.Point :=
  mordell_weil_special W data

end EllipticCurve.MordellWeil

end
