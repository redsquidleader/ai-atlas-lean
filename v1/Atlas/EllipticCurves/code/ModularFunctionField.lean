/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.ModularPolynomial
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup

noncomputable section

namespace ModularFunctionField

/-- The function field $\mathcal{F}(\Gamma)$ of a subgroup $\Gamma \leq \mathrm{SL}_2(\mathbb{Z})$:
the type of meromorphic modular functions $f : \mathcal{H} \to \mathbb{C}$ invariant under
$\Gamma$ and meromorphic at the cusps (Definition 19.2). -/
def FunctionField (Γ : Subgroup SL(2, ℤ)) : Type :=
  {f : ℍ → ℂ // IsModularFunction f Γ}

/-- The underlying function $\mathcal{H} \to \mathbb{C}$ of an element of `FunctionField Γ`. -/
def FunctionField.toFun {Γ : Subgroup SL(2, ℤ)} (f : FunctionField Γ) : ℍ → ℂ := f.val

/-- The proof that an element of `FunctionField Γ` is in fact a modular function for $\Gamma$. -/
def FunctionField.isModular {Γ : Subgroup SL(2, ℤ)} (f : FunctionField Γ) :
    IsModularFunction f.val Γ := f.property

/-- A function modular for the full group $\mathrm{SL}_2(\mathbb{Z})$ is a fortiori
modular for any subgroup $\Gamma$: meromorphicity is preserved and invariance under
$\Gamma$ follows from invariance under the whole group. -/
theorem isModularFunction_of_top {f : ℍ → ℂ} (Γ : Subgroup SL(2, ℤ))
    (hf : IsModularFunction f ⊤) : IsModularFunction f Γ where
  meromorphicOnH := hf.meromorphicOnH
  invariant := fun γ _ τ => hf.invariant γ (Subgroup.mem_top γ) τ
  meromorphicAtCusps := hf.meromorphicAtCusps

/-- The inclusion of function fields induced by the inclusion $\Gamma \leq \mathrm{SL}_2(\mathbb{Z})$,
sending a modular function for the full group to the same function viewed as a modular
function for $\Gamma$. -/
def inclusionFun (Γ : Subgroup SL(2, ℤ)) : FunctionField ⊤ → FunctionField Γ :=
  fun ⟨f, hf⟩ => ⟨f, isModularFunction_of_top Γ hf⟩

/-- The function field $\mathcal{F}(\Gamma)$ carries a (noncanonical) field structure
(Theorem 19.8). The construction proceeds by exhibiting pointwise sum, product,
and inverse operations on the underlying functions. -/
theorem instField_nonempty (Γ : Subgroup SL(2, ℤ)) : Nonempty (Field (FunctionField Γ)) := by sorry

/-- The chosen field structure on $\mathcal{F}(\Gamma)$ extracted from
`instField_nonempty` via choice. -/
noncomputable instance instField (Γ : Subgroup SL(2, ℤ)) : Field (FunctionField Γ) :=
  (instField_nonempty Γ).some

/-- The field $\mathbb{C}(j)$ of rational functions in Klein's $j$-invariant, realized as
the function field of the full modular group $\mathrm{SL}_2(\mathbb{Z})$ (Theorem 19.9). -/
abbrev RatFuncJ : Type := FunctionField ⊤

/-- The canonical ring homomorphism $\mathbb{C}(j) \hookrightarrow \mathcal{F}(\Gamma)$
making $\mathcal{F}(\Gamma)$ a $\mathbb{C}(j)$-algebra (Theorem 19.10). -/
noncomputable def algebraMap_ratFuncJ (Γ : Subgroup SL(2, ℤ)) : RatFuncJ →+* FunctionField Γ := by sorry

/-- The $\mathbb{C}(j)$-algebra structure on $\mathcal{F}(\Gamma)$ obtained from the
canonical ring homomorphism `algebraMap_ratFuncJ`. -/
instance instAlgebra (Γ : Subgroup SL(2, ℤ)) : Algebra RatFuncJ (FunctionField Γ) :=
  (algebraMap_ratFuncJ Γ).toAlgebra

/-- For any congruence subgroup $\Gamma$, the extension $\mathcal{F}(\Gamma)/\mathbb{C}(j)$
is finite-dimensional of degree at most $[\mathrm{SL}_2(\mathbb{Z}) : \Gamma]$
(Theorem 19.11). -/
theorem modularFunctionField_finite_extension
    (Γ : Subgroup SL(2, ℤ)) (hΓ : IsCongruenceSubgroup Γ) :
    FiniteDimensional RatFuncJ (FunctionField Γ) ∧
    Module.finrank RatFuncJ (FunctionField Γ) ≤ Γ.index := by sorry

end ModularFunctionField
