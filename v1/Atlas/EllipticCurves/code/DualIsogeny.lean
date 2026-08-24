/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.TorsionEndomorphism
import Atlas.EllipticCurves.code.DivisionPolynomials

open WeierstrassCurve.Affine

namespace DualIsogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {E₁ E₂ : WeierstrassCurve.Affine F}

/-- The dual isogeny `α̂ : E₂ → E₁` associated to an isogeny `α : E₁ → E₂`. -/
noncomputable abbrev dualIsogeny (α : Isogeny E₁ E₂) : Isogeny E₂ E₁ :=
  α.dualIsogeny

/-- Composing the dual isogeny `α̂` after `α` yields multiplication by `deg α` on `E₁`. -/
theorem dualIsogeny_comp (α : Isogeny E₁ E₂) :
    (dualIsogeny α).toAddMonoidHom.comp α.toAddMonoidHom =
      multiplicationByN E₁ (α.degree : ℤ) :=
  α.dualIsogeny_comp

/-- Uniqueness of the dual isogeny: any `β : E₂ → E₁` with `β ∘ α = [deg α]` on `E₁`
must equal `α̂`. -/
theorem dualIsogeny_unique (α : Isogeny E₁ E₂) (β : Isogeny E₂ E₁)
    (hβ : β.toAddMonoidHom.comp α.toAddMonoidHom =
      multiplicationByN E₁ (α.degree : ℤ)) :
    β = dualIsogeny α := by
  exact Isogeny.ext
    (α.dualIsogeny_unique β hβ)
    ((α.degree_of_dual_property β hβ).trans α.degree_dualIsogeny.symm)

/-- Composing `α` after its dual `α̂` yields multiplication by `deg α` on `E₂`. -/
theorem comp_dualIsogeny (α : Isogeny E₁ E₂) :
    α.toAddMonoidHom.comp (dualIsogeny α).toAddMonoidHom =
      multiplicationByN E₂ (α.degree : ℤ) :=
  α.comp_dualIsogeny

/-- The dual isogeny has the same degree as the original isogeny. -/
theorem degree_dualIsogeny (α : Isogeny E₁ E₂) :
    (dualIsogeny α).degree = α.degree :=
  α.degree_dualIsogeny

/-- The dual of the dual recovers the original isogeny as an additive map (involutivity). -/
theorem dualIsogeny_dualIsogeny (α : Isogeny E₁ E₂) :
    (dualIsogeny (dualIsogeny α)).toAddMonoidHom =
      α.toAddMonoidHom :=
  α.dualIsogeny_dualIsogeny

/-- The multiplication-by-`n` isogeny is self-dual: its dual is again multiplication by `n`. -/
theorem multiplicationByN_self_dual
    {E : WeierstrassCurve.Affine F} (n : ℤ) (hn : n ≠ 0) :
    (Isogeny.multiplicationByN_isogeny E n hn).dualIsogeny.toAddMonoidHom =
      multiplicationByN E n :=
  Isogeny.multiplicationByN_self_dual E n hn

end DualIsogeny

namespace DualIsogenyExt

variable {F : Type*} [Field F] [DecidableEq F]
variable {E₁ E₂ : WeierstrassCurve.Affine F}

open WeierstrassCurve.Affine

/-- An isogeny `E₁ → E₂` or the zero map (which is not an isogeny, but is needed to make
the set of "isogenies-or-zero" into a monoid). -/
inductive IsogenyOrZero (E₁ E₂ : WeierstrassCurve.Affine F) where
  | zero : IsogenyOrZero E₁ E₂
  | ofIsogeny (α : Isogeny E₁ E₂) : IsogenyOrZero E₁ E₂

/-- Converts an `IsogenyOrZero` to the underlying additive group homomorphism. -/
def IsogenyOrZero.toAddMonoidHom : IsogenyOrZero E₁ E₂ → (E₁.Point →+ E₂.Point)
  | .zero => 0
  | .ofIsogeny α => α.toAddMonoidHom

/-- The degree of an `IsogenyOrZero` (zero for the zero map, the degree of the isogeny otherwise). -/
def IsogenyOrZero.deg : IsogenyOrZero E₁ E₂ → ℕ
  | .zero => 0
  | .ofIsogeny α => α.degree

/-- The dual of an `IsogenyOrZero`: zero stays zero, an isogeny is sent to its dual. -/
noncomputable def IsogenyOrZero.dual : IsogenyOrZero E₁ E₂ → IsogenyOrZero E₂ E₁
  | .zero => .zero
  | .ofIsogeny α => .ofIsogeny α.dualIsogeny

/-- The dual of the zero map is the zero map. -/
@[simp]
theorem IsogenyOrZero.dual_zero :
    (IsogenyOrZero.zero : IsogenyOrZero E₁ E₂).dual = IsogenyOrZero.zero :=
  rfl

/-- The degree of the zero map is `0`. -/
@[simp]
theorem IsogenyOrZero.deg_zero :
    (IsogenyOrZero.zero : IsogenyOrZero E₁ E₂).deg = 0 :=
  rfl

/-- The dual of `ofIsogeny α` is `ofIsogeny α̂`. -/
@[simp]
theorem IsogenyOrZero.dual_ofIsogeny (α : Isogeny E₁ E₂) :
    (IsogenyOrZero.ofIsogeny α).dual = IsogenyOrZero.ofIsogeny α.dualIsogeny :=
  rfl

/-- The degree of `ofIsogeny α` equals the degree of `α`. -/
@[simp]
theorem IsogenyOrZero.deg_ofIsogeny (α : Isogeny E₁ E₂) :
    (IsogenyOrZero.ofIsogeny α).deg = α.degree :=
  rfl

end DualIsogenyExt

namespace IsogenyDecomposition

variable {F : Type*} [Field F] [DecidableEq F]

/-- If an isogeny `α` has degree `> 1` and `p` is a prime dividing `deg α`, then `α` factors
through an intermediate curve as `α = γ ∘ β` with `β` of degree `p`. -/
theorem isogeny_prime_factor
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : 1 < α.degree)
    (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ α.degree) :
    ∃ (E_mid : WeierstrassCurve.Affine F)
      (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂),
      β.degree = p ∧
      0 < γ.degree ∧
      γ.degree * β.degree = α.degree ∧
      γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom :=
  Isogeny.prime_factor_aux α hdeg p hp hdvd

/-- Any isogeny `α` of degree `> 1` decomposes as a chain of isogenies, each of prime degree,
whose composition equals `α`. -/
theorem isogeny_prime_degree_decomposition
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : 1 < α.degree) :
    ∃ (chain : IsogenyChain E₁ E₂),
      chain.allPrimeDegree ∧
      chain.compose = α.toAddMonoidHom :=
  _root_.isogeny_prime_degree_decomposition (F := F) α hdeg

end IsogenyDecomposition
