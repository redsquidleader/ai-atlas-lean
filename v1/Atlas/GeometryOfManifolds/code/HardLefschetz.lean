/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.AdvancedKahler

set_option autoImplicit false

open DifferentialFormSpace


/-- A Kähler manifold with Hodge number data, additionally tracking the integral
$\int_M \omega^n$ of the top power of the Kähler form. -/
class HasKahlerHodgeNumbers
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasHodgeNumbers Ω VF inst where
  omega_n_integral : ℝ


/-- Axiom: $\int_M \omega^n > 0$ on a Kähler manifold (since $\omega^n$ is a volume form). -/
theorem HasKahlerHodgeNumbers.omega_n_integral_pos_ax
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (hH : @HasKahlerHodgeNumbers Ω VF inst)
    : 0 < hH.omega_n_integral := by sorry

/-- Axiom: if $h^{n,n} = 0$ then $\omega^n$ is exact and Stokes implies $\int_M \omega^n = 0$. -/
theorem HasKahlerHodgeNumbers.stokes_exact_vanishes_ax
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (hH : @HasKahlerHodgeNumbers Ω VF inst)
    : hH.hodge hH.complexDim hH.complexDim = 0 → hH.omega_n_integral = 0 := by sorry

/-- Axiom: if $h^{p,p} = 0$ for some $p \leq n$, then $\omega^p$ is exact and the integral
$\int_M \omega^n = 0$ (via the Hard Lefschetz factorization $\omega^n = L^{n-p} \omega^p$). -/
theorem HasKahlerHodgeNumbers.omega_factor_vanishes_ax
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (hH : @HasKahlerHodgeNumbers Ω VF inst)
    : ∀ (p : ℕ), p ≤ hH.complexDim → hH.hodge p p = 0 → hH.omega_n_integral = 0 := by sorry


/-- Instance-form version: $\int_M \omega^n > 0$. -/
theorem HasKahlerHodgeNumbers.omega_n_integral_pos_thm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hH : @HasKahlerHodgeNumbers Ω VF inst]
    : 0 < hH.omega_n_integral :=
  hH.omega_n_integral_pos_ax

/-- Instance-form version of the Stokes vanishing implication for $h^{n,n} = 0$. -/
theorem HasKahlerHodgeNumbers.stokes_exact_vanishes_thm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hH : @HasKahlerHodgeNumbers Ω VF inst]
    : hH.hodge hH.complexDim hH.complexDim = 0 → hH.omega_n_integral = 0 :=
  hH.stokes_exact_vanishes_ax

/-- Instance-form version: $h^{p,p} = 0$ for any $p \leq n$ forces $\int_M \omega^n = 0$. -/
theorem HasKahlerHodgeNumbers.omega_factor_vanishes_thm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hH : @HasKahlerHodgeNumbers Ω VF inst]
    : ∀ (p : ℕ), p ≤ hH.complexDim → hH.hodge p p = 0 → hH.omega_n_integral = 0 :=
  hH.omega_factor_vanishes_ax


/-- On a compact Kähler manifold, the volume class is nonzero: $h^{n,n} \geq 1$. -/
theorem HasKahlerHodgeNumbers.volume_class_nonzero
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hH : @HasKahlerHodgeNumbers Ω VF inst]
    : 1 ≤ hH.hodge hH.complexDim hH.complexDim := by

  by_contra h_contra
  push Not at h_contra

  have h_zero : hH.hodge hH.complexDim hH.complexDim = 0 := Nat.lt_one_iff.mp h_contra

  have h_integral_zero : hH.omega_n_integral = 0 :=
    hH.stokes_exact_vanishes_thm h_zero

  have h_integral_pos : 0 < hH.omega_n_integral :=
    hH.omega_n_integral_pos_thm

  linarith


/-- Each Hodge number $h^{p,p}$ for $p \leq n$ is at least 1 on a compact Kähler manifold,
since $[\omega^p] \neq 0$ in $H^{p,p}$. -/
theorem HasKahlerHodgeNumbers.omega_power_factoring
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hH : @HasKahlerHodgeNumbers Ω VF inst]
    (p : ℕ) (hp : p ≤ hH.complexDim) :
    1 ≤ hH.hodge p p := by

  by_contra h_contra
  push Not at h_contra
  have h_zero : hH.hodge p p = 0 := Nat.lt_one_iff.mp h_contra

  have h_integral_zero : hH.omega_n_integral = 0 :=
    hH.omega_factor_vanishes_thm p hp h_zero

  have h_integral_pos : 0 < hH.omega_n_integral :=
    hH.omega_n_integral_pos_thm

  linarith


/-- A cohomology theory equipped with the Hard Lefschetz pairing $Q(n,k)$ on $H^k$,
biadditive in both arguments and ℝ-linear in the left. -/
class HasHardLefschetzPairing
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomologyWithLefschetz Ω VF inst where
  Q : ∀ (_n k : ℕ), H k → H k → ℝ
  Q_add_left : ∀ (n k : ℕ) (α₁ α₂ β : H k),
    Q n k (@HAdd.hAdd _ _ _ (@instHAdd _ (H_addCommGroup k).toAddCommMonoid.toAdd) α₁ α₂) β =
    Q n k α₁ β + Q n k α₂ β
  Q_add_right : ∀ (n k : ℕ) (α β₁ β₂ : H k),
    Q n k α (@HAdd.hAdd _ _ _ (@instHAdd _ (H_addCommGroup k).toAddCommMonoid.toAdd) β₁ β₂) =
    Q n k α β₁ + Q n k α β₂
  Q_smul_left : ∀ (n k : ℕ) (r : ℝ) (α β : H k),
    Q n k (@HSMul.hSMul ℝ _ _ (@instHSMul _ _ (H_module k).toSMul) r α) β =
    r * Q n k α β


/-- The Lefschetz decomposition of cohomology: every class $\alpha \in H^k$ decomposes as
$\alpha = \sum_r L^r \alpha_{k-2r}^{\text{prim}}$, where the primitive components are
characterized by $L^{n-(k-2r)+1} \alpha_{k-2r}^{\text{prim}} = 0$. -/
class HasLefschetzDecomposition
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomologyWithLefschetz Ω VF inst where
  prim_component : ∀ (_n k r : ℕ),
    @LinearMap ℝ ℝ _ _ (RingHom.id ℝ) (H k) (H (k - 2 * r))
      (H_addCommGroup k).toAddCommMonoid (H_addCommGroup (k - 2 * r)).toAddCommMonoid
      (H_module k) (H_module (k - 2 * r))
  prim_component_is_primitive : ∀ (n k r : ℕ) (_hkn : k ≤ n) (_hr : 2 * r ≤ k)
    (α : H k),
    L_map (k - 2 * r) (n - (k - 2 * r) + 1) (prim_component n k r α) =
      @OfNat.ofNat _ 0 (@Zero.toOfNat0 _
        (H_addCommGroup ((k - 2 * r) + 2 * (n - (k - 2 * r) + 1))).toZero)
  reconstruct : ∀ (_n k : ℕ), H k → H k
  reconstruct_eq : ∀ (n k : ℕ) (_hkn : k ≤ n) (α : H k),
    reconstruct n k α = α
  prim_component_injective : ∀ (n k : ℕ) (_hkn : k ≤ n) (α : H k),
    (∀ r, 2 * r ≤ k → prim_component n k r α =
      @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (H_addCommGroup (k - 2 * r)).toZero)) →
    α = @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (H_addCommGroup k).toZero)
