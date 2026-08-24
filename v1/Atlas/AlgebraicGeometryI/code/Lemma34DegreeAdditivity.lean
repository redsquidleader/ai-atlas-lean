/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Quotient.Basic

universe u v

namespace Lemma34

/-- Degree of a finitely generated torsion-free module over a Dedekind
domain (Lec 22, Lemma 34 setting). -/
noncomputable def degTorsionFree (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [NoZeroSMulDivisors R M] : ℤ := by sorry

/-- The degree of a torsion-free module is an isomorphism invariant. -/
theorem degTorsionFree_congr
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁] [NoZeroSMulDivisors R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₂] [NoZeroSMulDivisors R M₂]
    (e : M₁ ≃ₗ[R] M₂) :
    degTorsionFree R M₁ = degTorsionFree R M₂ := by sorry

/-- Base case of degree additivity: if `M'/N` has length one (a simple
extension), then `deg M' = deg N + 1`. -/
theorem degTorsionFree_simple_ext
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {M' : Type*} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [NoZeroSMulDivisors R M']
    (N : Submodule R M') [Module.Finite R N] [NoZeroSMulDivisors R N]
    (hlen : Module.length R (M' ⧸ N) = 1) :
    degTorsionFree R M' = degTorsionFree R N + 1 := by sorry

/-- Inductive step ingredient: given `N ⊆ M'` with quotient of torsion
length `n + 1`, there exists an intermediate `N ≤ N' ⊆ M'` such that
`N'/N` has length one and `M'/N'` has torsion length `n`. -/
theorem intermediate_submodule_exists
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {M' : Type*} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [NoZeroSMulDivisors R M']
    (N : Submodule R M') [Module.Finite R N] [NoZeroSMulDivisors R N]
    (n : ℕ) (hn : 0 < n)
    (hlen : Module.length R (M' ⧸ N) = ↑(n + 1))
    (htor : Module.IsTorsion R (M' ⧸ N)) :
    ∃ (N' : Submodule R M') (_ : Module.Finite R N') (_ : NoZeroSMulDivisors R N'),
      N ≤ N' ∧
      Module.length R (↥N' ⧸ (N.comap N'.subtype)) = 1 ∧
      Module.length R (M' ⧸ N') = ↑n ∧
      Module.IsTorsion R (M' ⧸ N') := by sorry

/-- Helper: `NoZeroSMulDivisors` transfers along a linear equivalence. -/
theorem noZeroSMulDivisors_of_linearEquiv
    {R' : Type*} [CommRing R'] [IsDomain R']
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R' M₁]
    [AddCommGroup M₂] [Module R' M₂] [NoZeroSMulDivisors R' M₂]
    (e : M₁ ≃ₗ[R'] M₂) : NoZeroSMulDivisors R' M₁ where
  eq_zero_or_eq_zero_of_smul_eq_zero {r x} h := by
    have h' : r • e x = 0 := by rw [← e.map_smul, h, map_zero]
    rcases smul_eq_zero.mp h' with hr | hx
    · left; exact hr
    · right; exact e.injective (by rw [hx, map_zero])

/-- Helper: the torsion property transfers along a linear equivalence. -/
lemma Module.IsTorsion.of_linearEquiv {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (h : Module.IsTorsion R N) : Module.IsTorsion R M := by
  intro x
  obtain ⟨⟨a, ha⟩, hax⟩ := h (x := e x)
  refine ⟨⟨a, ha⟩, ?_⟩
  apply e.injective
  simp only [map_zero]
  change e ((a : R) • x) = 0
  rw [map_smul]
  exact hax

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- Induction predicate for Lemma 34: for any submodule `N ⊆ M'` with
torsion quotient of length `k`, the degrees differ by `k`. -/
def P_lemma34 (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (M' : Type*) [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [NoZeroSMulDivisors R M'] (k : ℕ) : Prop :=
  ∀ (N : Submodule R M') [Module.Finite R N] [NoZeroSMulDivisors R N],
    0 < k →
    Module.length R (M' ⧸ N) = ↑k →
    Module.IsTorsion R (M' ⧸ N) →
    degTorsionFree R M' = degTorsionFree R N + (k : ℤ)

/-- Induction on length: the predicate `P_lemma34` holds for every
`k`. -/
theorem P_lemma34_holds
    {M' : Type*} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [NoZeroSMulDivisors R M'] :
    ∀ k, P_lemma34 R M' k := by
  intro k
  exact Nat.strongRecOn k fun k ih => by
    unfold P_lemma34 at ih ⊢
    intro N inst_fin inst_nzsd hk hlen htor
    match k with
    | 0 => omega
    | 1 =>

      have h1 : Module.length R (M' ⧸ N) = 1 := by simpa using hlen
      have := degTorsionFree_simple_ext N h1
      push_cast; linarith
    | n + 2 =>

      have hn_pos : 0 < n + 1 := Nat.succ_pos n
      obtain ⟨N', hfin', hnzsd', hle_N_N', hlen_N'_N, hlen', htor'⟩ :=
        intermediate_submodule_exists N (n + 1) hn_pos hlen htor

      haveI : Module.Finite R ↥(N.comap N'.subtype) :=
        Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle_N_N').symm
      haveI : NoZeroSMulDivisors R ↥(N.comap N'.subtype) :=
        noZeroSMulDivisors_of_linearEquiv (Submodule.comapSubtypeEquivOfLe hle_N_N')

      have step1 := degTorsionFree_simple_ext (N.comap N'.subtype) hlen_N'_N

      have step2 := degTorsionFree_congr (Submodule.comapSubtypeEquivOfLe hle_N_N')

      have hdeg' : degTorsionFree R ↥N' = degTorsionFree R ↥N + 1 := by linarith

      have h_lt : n + 1 < n + 2 := Nat.lt_succ_of_le le_rfl
      have ih_result := ih (n + 1) h_lt N' hn_pos hlen' htor'

      push_cast at ih_result ⊢; linarith

/-- Submodule version of Lemma 34: for `N ⊆ M'` torsion-free with
`M'/N` torsion of length `k`, the degrees satisfy
`deg M' = deg N + k`. -/
theorem lemma34_degTorsionFree
    {M' : Type*} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [NoZeroSMulDivisors R M']
    (N : Submodule R M') [Module.Finite R N] [NoZeroSMulDivisors R N]
    (k : ℕ) (hk : 0 < k)
    (hlen : Module.length R (M' ⧸ N) = ↑k)
    (htor : Module.IsTorsion R (M' ⧸ N)) :
    degTorsionFree R M' = degTorsionFree R N + (k : ℤ) :=
  P_lemma34_holds k N hk hlen htor

end Lemma34

/-- Lec 22, Lemma 34 (degree additivity): for a short exact sequence
`0 → E → E' → T → 0` of finite modules over a Dedekind domain `R`,
with `E, E'` torsion-free and `T` torsion of finite length,
`deg E' = deg E + length(T)`. -/
theorem lemma34_degree_additivity
    (R : Type u) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {E E' T : Type v}
    [AddCommGroup E] [Module R E] [Module.Finite R E] [NoZeroSMulDivisors R E]
    [AddCommGroup E'] [Module R E'] [Module.Finite R E'] [NoZeroSMulDivisors R E']
    [AddCommGroup T] [Module R T]
    (hT : Module.IsTorsion R T)
    (hTfin : IsFiniteLength R T)
    (f : E →ₗ[R] E') (g : E' →ₗ[R] T)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    Lemma34.degTorsionFree R E' =
      Lemma34.degTorsionFree R E + (Module.length R T).toNat := by
  open Lemma34 in

  have hker_eq_range : g.ker = f.range := LinearMap.exact_iff.mp hex

  let φ : (E' ⧸ f.range) ≃ₗ[R] T :=
    (Submodule.quotEquivOfEq _ _ hker_eq_range.symm).trans (g.quotKerEquivOfSurjective hg)

  have hlen_ne_top : Module.length R T ≠ ⊤ := Module.length_ne_top_iff.mpr hTfin

  set k := (Module.length R T).toNat with hk_def

  have hlen_T_eq : Module.length R T = ↑k := (ENat.coe_toNat hlen_ne_top).symm

  by_cases hk0 : k = 0
  ·
    simp only [hk0, Nat.cast_zero, add_zero]

    have hlen_zero : Module.length R T = 0 := by rw [hlen_T_eq, hk0]; simp
    have : Subsingleton T := Module.length_eq_zero_iff.mp hlen_zero

    have hf_surj : Function.Surjective f := by
      have : g.ker = ⊤ := by ext x; simp [Subsingleton.eq_zero]
      exact LinearMap.range_eq_top.mp (by rw [← hker_eq_range]; exact this)

    exact (degTorsionFree_congr (LinearEquiv.ofBijective f ⟨hf, hf_surj⟩)).symm
  ·
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0

    haveI : NoZeroSMulDivisors R f.range :=
      noZeroSMulDivisors_of_linearEquiv (LinearEquiv.ofInjective f hf).symm
    haveI : Module.Finite R f.range := Module.Finite.range f

    have hlen_quot : Module.length R (E' ⧸ f.range) = ↑k := by
      rw [φ.length_eq, hlen_T_eq]

    have htor_quot : Module.IsTorsion R (E' ⧸ f.range) :=
      Module.IsTorsion.of_linearEquiv φ hT

    have h1 := lemma34_degTorsionFree f.range k hk_pos hlen_quot htor_quot

    have h2 : degTorsionFree R ↥(f.range) = degTorsionFree R E :=
      (degTorsionFree_congr (LinearEquiv.ofInjective f hf)).symm

    linarith
