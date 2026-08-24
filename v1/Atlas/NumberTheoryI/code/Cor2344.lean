/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.TateCohomology
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic

noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

instance tateH0.inhabited (A : Rep k G) : Inhabited (tateH0 A) := ⟨0⟩

instance tateMinus1.inhabited (A : Rep k G) : Inhabited (tateMinus1 A) := ⟨0⟩

theorem herbrandQuotient_eq_one_of_finite' [IsCyclic G] (A : Rep k G)
    [Finite A] [Fintype (tateH0 A)] [Fintype (tateMinus1 A)] :
    herbrandQuotient A = 1 := by
  have heq := herbrand_quotient_eq_one_of_finite A
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at heq
  unfold herbrandQuotient
  rw [heq]
  have hpos : (0 : ℚ) < Fintype.card (tateMinus1 A) := by
    exact_mod_cast Fintype.card_pos (α := tateMinus1 A)
  exact div_self hpos.ne'

instance tateH0.finite (A : Rep k G) [Finite A] : Finite (tateH0 A) := by
  unfold tateH0
  haveI : Finite A.ρ.invariants :=
    Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Finite.of_surjective (Submodule.Quotient.mk (p := normImageInInvariants A))
    (Submodule.Quotient.mk_surjective _)

instance tateMinus1.finite (A : Rep k G) [Finite A] : Finite (tateMinus1 A) := by
  unfold tateMinus1
  haveI : Finite (LinearMap.ker (normMap k G A)) :=
    Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Finite.of_surjective (Submodule.Quotient.mk (p := augInKerNorm A))
    (Submodule.Quotient.mk_surjective _)

set_option checkBinderAnnotations false in
theorem finite_of_shortExact_torsion_fg {G₀ : Type} [Group G₀] [Fintype G₀]
    {S : ShortComplex (Rep ℤ G₀)} (hS : S.ShortExact)
    (htors : Module.IsTorsion ℤ S.X₁) (hfg : Module.Finite ℤ S.X₂) :
    Finite (S.X₁ : Rep ℤ G₀) := by

  let φ : ↑S.X₁ →+ ↑S.X₂ :=
    { toFun := S.f.hom
      map_zero' := by simp [map_zero]
      map_add' := by simp [map_add] }

  let ψ : ↑S.X₁ →ₗ[ℤ] ↑S.X₂ := φ.toIntLinearMap

  have hinj : Function.Injective ψ := by
    intro a b hab
    have := hS.mono_f
    exact (Rep.mono_iff_injective S.f).mp this hab

  haveI : IsNoetherian ℤ S.X₂ := isNoetherian_of_isNoetherianRing_of_finite ℤ (↑S.X₂)

  haveI : Module.Finite ℤ S.X₁ := Module.Finite.of_injective ψ hinj

  exact Module.finite_of_fg_torsion _ htors

theorem herbrandQuotient_eq_shortExact_torsion {G₀ : Type} [Group G₀] [Fintype G₀] [IsCyclic G₀]
    {S : ShortComplex (Rep ℤ G₀)} (hS : S.ShortExact)
    (htors : Module.IsTorsion ℤ S.X₁)
    (hfg : Module.Finite ℤ S.X₂)
    [Fintype (tateH0 S.X₂)] [Fintype (tateMinus1 S.X₂)]
    [Fintype (tateH0 S.X₃)] [Fintype (tateMinus1 S.X₃)] :
    herbrandQuotient S.X₂ = herbrandQuotient S.X₃ := by

  haveI : Finite (S.X₁ : Rep ℤ G₀) := finite_of_shortExact_torsion_fg hS htors hfg
  haveI : Fintype (tateH0 S.X₁) := Fintype.ofFinite _
  haveI : Fintype (tateMinus1 S.X₁) := Fintype.ofFinite _

  have hmult := herbrandQuotient_multiplicative hS

  have hone := herbrandQuotient_eq_one_of_finite' S.X₁
  rw [hmult, hone, one_mul]

theorem herbrandQuotient_trivial_pow_clean {G₀ : Type} [Group G₀] [Fintype G₀] [IsCyclic G₀]
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M]
    [Fintype (tateH0 (Rep.trivial ℤ G₀ M))]
    [Fintype (tateMinus1 (Rep.trivial ℤ G₀ M))] :
    herbrandQuotient (Rep.trivial ℤ G₀ M) =
      (Fintype.card G₀ : ℚ) ^ (Module.finrank ℤ M) := by

  set Q := M ⧸ Submodule.torsion ℤ M with hQ_def
  haveI : Module.IsTorsionFree ℤ Q := Submodule.QuotientTorsion.instIsTorsionFree
  haveI : Module.Finite ℤ Q := Module.Finite.quotient ℤ (Submodule.torsion ℤ M)
  haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'

  let n := Module.finrank ℤ Q
  let eQ : Q ≃ₗ[ℤ] (Fin n → ℤ) := (Module.finBasis ℤ Q).equivFun

  have hrank : Module.finrank ℤ M = n := by
    simp only [Module.finrank, n]
    congr 1
    exact (rank_quotient_eq_of_le_torsion (le_refl (Submodule.torsion ℤ M))).symm

  let β : M →ₗ[ℤ] (Fin n → ℤ) := eQ.toLinearMap.comp (Submodule.torsion ℤ M).mkQ

  let α : Rep.trivial ℤ G₀ M ⟶ Rep.trivial ℤ G₀ (Fin n → ℤ) := Rep.trivialHom β

  haveI : IsNoetherian ℤ M := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  haveI : Module.Finite ℤ (Submodule.torsion ℤ M) :=
    Module.IsNoetherian.finite ℤ (↥(Submodule.torsion ℤ M))
  haveI hfin_tor : Finite (↑(Submodule.torsion ℤ M)) :=
    Module.finite_of_fg_torsion _ Submodule.torsion_isTorsion

  have hβ_surj : Function.Surjective β := by
    intro p
    obtain ⟨q, hq⟩ := eQ.surjective p
    obtain ⟨m, hm⟩ := Submodule.mkQ_surjective _ q
    exact ⟨m, by subst hm; subst hq; rfl⟩

  haveI hfin_ker : Finite (Limits.kernel α : Rep ℤ G₀) := by

    have h_inj : Function.Injective (Limits.kernel.ι α).hom := by
      rw [← Rep.mono_iff_injective]; exact inferInstance


    have h_in_tor : ∀ x : (Limits.kernel α : Rep ℤ G₀),
        (Limits.kernel.ι α).hom x ∈ Submodule.torsion ℤ M := by
      intro x
      have hcond := Limits.kernel.condition (f := α)
      have hx : (α.hom) ((Limits.kernel.ι α).hom x) = 0 := by
        have := congr_arg Rep.Hom.hom hcond
        exact congr_fun (congr_arg DFunLike.coe this) x


      change β ((Limits.kernel.ι α).hom x) = 0 at hx
      have hmkq : (Submodule.torsion ℤ M).mkQ ((Limits.kernel.ι α).hom x) = 0 := by

        exact eQ.map_eq_zero_iff.mp hx
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmkq

    let ι_tor : ↑(Limits.kernel α : Rep ℤ G₀) → ↥(Submodule.torsion ℤ M) :=
      fun x => ⟨(Limits.kernel.ι α).hom x, h_in_tor x⟩
    have h_ι_tor_inj : Function.Injective ι_tor := by
      intro a b hab
      simp only [ι_tor, Subtype.mk.injEq] at hab
      exact h_inj hab
    exact Finite.of_injective ι_tor h_ι_tor_inj

  haveI hfin_coker : Finite (Limits.cokernel α : Rep ℤ G₀) := by
    haveI : Epi α := by
      rw [Rep.epi_iff_surjective]
      show Function.Surjective α.hom
      exact hβ_surj
    have hz := Limits.isZero_cokernel_of_epi α
    haveI : Subsingleton (Limits.cokernel α : Rep ℤ G₀) := by
      constructor; intro a b
      have : ∀ x : (Limits.cokernel α : Rep ℤ G₀), x = 0 := by
        intro x
        have key := congr_arg (fun g =>
          (show Limits.cokernel α ⟶ Limits.cokernel α from g).hom)
          (hz.eq_of_src (𝟙 (Limits.cokernel α)) 0)
        have := congr_fun (congr_arg DFunLike.coe key) x
        simpa using this
      rw [this a, this b]
    exact Finite.of_subsingleton

  haveI : Fintype (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ))) := Fintype.ofFinite _
  haveI : Fintype (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) := Fintype.ofFinite _
  have h_MZ : herbrandQuotient (Rep.trivial ℤ G₀ M) =
      herbrandQuotient (Rep.trivial ℤ G₀ (Fin n → ℤ)) := herbrandQuotient_eq_of_finite_kernel_cokernel α

  have h_fin : herbrandQuotient (Rep.trivial ℤ G₀ (Fin n → ℤ)) =
      (Fintype.card G₀ : ℚ) ^ n := herbrandQuotient_trivial_finFun G₀ n

  rw [h_MZ, h_fin, hrank]

end TateCohomology
