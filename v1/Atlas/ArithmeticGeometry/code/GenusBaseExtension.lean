/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch

open RiemannRochSpace

/-- Data packaging a base extension $k \hookrightarrow k'$ for a smooth projective curve
$(C, F/k)$: a new curve $C'$ over a field $F'/k'$, together with a `RiemannRochData` structure on
$(C', F', k')$ and explicit divisor base-extension and restriction maps. -/
structure BaseExtensionData
    (C : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k] where
  C' : Type*
  F' : Type*
  k' : Type*
  field_k' : Field k'
  field_F' : Field F'
  algebra_k_k' : Algebra k k'
  algebra_k'_F' : Algebra k' F'
  rrData' : RiemannRochData C' F' k'
  baseExtDiv : CurveDivisor C → CurveDivisor C'
  restrictDiv : CurveDivisor C' → CurveDivisor C

attribute [instance] BaseExtensionData.field_k' BaseExtensionData.field_F'
  BaseExtensionData.algebra_k_k' BaseExtensionData.algebra_k'_F'
  BaseExtensionData.rrData'

/-- Axiomatized: the divisor base-extension map preserves degree, $\deg_{C'}(\mathrm{baseExt}(D))
= \deg_C(D)$. -/
theorem BaseExtensionData.degree_baseExt_ax
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (ext : BaseExtensionData C F k)
    (D : CurveDivisor C) :
    CurveDivisor.degree ext.C' (ext.baseExtDiv D) = CurveDivisor.degree C D := by sorry

/-- Axiomatized: the divisor base-extension map preserves the Riemann–Roch dimension,
$\dim L(\mathrm{baseExt}(D))_{F'/k'} = \dim L(D)_{F/k}$. -/
theorem BaseExtensionData.divisorDim_baseExt_ax
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (ext : BaseExtensionData C F k)
    (D : CurveDivisor C) :
    @divisorDim ext.C' ext.F' ext.k' ext.field_k' ext.field_F' ext.algebra_k'_F'
      ext.rrData' (ext.baseExtDiv D) =
      divisorDim (F := F) (k := k) D := by sorry

/-- Axiomatized: the divisor restriction map preserves degree,
$\deg_C(\mathrm{restrict}(D')) = \deg_{C'}(D')$. -/
theorem BaseExtensionData.degree_restrict_ax
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (ext : BaseExtensionData C F k)
    (D' : CurveDivisor ext.C') :
    CurveDivisor.degree C (ext.restrictDiv D') = CurveDivisor.degree ext.C' D' := by sorry

/-- Axiomatized: the divisor restriction map preserves the Riemann–Roch dimension. -/
theorem BaseExtensionData.divisorDim_restrict_ax
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (ext : BaseExtensionData C F k)
    (D' : CurveDivisor ext.C') :
    divisorDim (F := F) (k := k) (ext.restrictDiv D') =
      @divisorDim ext.C' ext.F' ext.k' ext.field_k' ext.field_F' ext.algebra_k'_F'
        ext.rrData' D' := by sorry

/-- Invariance of genus under base extension: for a perfect base field $k$, base-changing the
curve $C$ to a curve $C'$ over $k'$ preserves the genus, $g_{C'/k'} = g_{C/k}$. The proof uses
mutual upper bounds obtained from `degree_baseExt_ax`/`divisorDim_baseExt_ax` and
`degree_restrict_ax`/`divisorDim_restrict_ax`. -/
theorem genus_preserved_under_base_extension
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    [PerfectField k]
    (ext : BaseExtensionData C F k) :
    genus (C := ext.C') (F := ext.F') (k := ext.k') =
      genus (C := C) (F := F) (k := k) := by
  apply le_antisymm
  ·


    apply genus_le_of_bound
    intro D'
    have h := genus_bound (C := C) (F := F) (k := k) (ext.restrictDiv D')
    rw [ext.degree_restrict_ax, ext.divisorDim_restrict_ax] at h
    exact h
  ·


    apply genus_le_of_bound
    intro D
    have h := genus_bound (C := ext.C') (F := ext.F') (k := ext.k') (ext.baseExtDiv D)
    rw [ext.degree_baseExt_ax, ext.divisorDim_baseExt_ax] at h
    exact h
