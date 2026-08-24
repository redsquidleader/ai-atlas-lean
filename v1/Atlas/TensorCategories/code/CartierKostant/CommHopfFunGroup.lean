/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.CartierKostant.Theorems
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v

namespace Corollary1278

/-- For a finite `k`-algebra `H` over an algebraically closed field `k`, the structure map
`k → H/𝔪` to any residue field at a maximal ideal is an algebra isomorphism. -/
noncomputable def residueFieldEquivOfAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type v) [CommRing H] [Algebra k H] [Module.Finite k H]
    (I : MaximalSpectrum H) : k ≃ₐ[k] (H ⧸ I.asIdeal) := by
  haveI : IsDomain (H ⧸ I.asIdeal) := Ideal.Quotient.isDomain I.asIdeal
  haveI : Module.Finite k (H ⧸ I.asIdeal) :=
    Module.Finite.quotient k (I.asIdeal.restrictScalars k)
  haveI : Algebra.IsIntegral k (H ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ I.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- For a finite-dimensional commutative Hopf algebra `H` over `k`, the maximal spectrum
of `H` inherits a group structure (dual to the comultiplication on `H`). -/
def maximalSpectrumGroupOfHopfAlgebra
    (k : Type u) [Field k]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] :
    Group (MaximalSpectrum H) := by sorry

end Corollary1278

section FunAlgEquivEquiv

variable {k : Type u} [Field k] {G₁ : Type v} [Fintype G₁] [DecidableEq G₁]
  {G₂ : Type v} [Fintype G₂] [DecidableEq G₂]

/-- A `k`-algebra equivalence `(G₁ → k) ≃ₐ[k] (G₂ → k)` between finite product algebras
of copies of `k` induces a map `G₂ → G₁` by identifying evaluation algebra homomorphisms
on the codomain with those on the domain. -/
noncomputable def funAlgEquivInducedMap (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) : G₂ → G₁ := fun g₂ =>
  (AlgHom.eq_piEvalAlgHom ((Pi.evalAlgHom k (fun _ : G₂ => k) g₂).comp e.toAlgHom)).choose

omit [DecidableEq G₁] [Fintype G₂] [DecidableEq G₂] in
/-- Defining property of `funAlgEquivInducedMap`: evaluation of `f` at the induced point
`funAlgEquivInducedMap e g₂` agrees with evaluation of `e f` at `g₂`. -/
lemma funAlgEquivInducedMap_spec (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) (g₂ : G₂) (f : G₁ → k) :
    f (funAlgEquivInducedMap e g₂) = (e f) g₂ := by
  have := (AlgHom.eq_piEvalAlgHom
    ((Pi.evalAlgHom k (fun _ : G₂ => k) g₂).comp e.toAlgHom)).choose_spec
  have h := congr_fun (congr_arg DFunLike.coe this) f
  simp only [Pi.evalAlgHom_apply, AlgHom.comp_apply] at h
  exact h.symm

omit [DecidableEq G₁] [Fintype G₂] in
/-- The induced map `funAlgEquivInducedMap e : G₂ → G₁` from an algebra equivalence is
injective. -/
lemma funAlgEquivInducedMap_injective (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) :
    Function.Injective (funAlgEquivInducedMap e) := by
  intro g₂ g₂' heq
  by_contra hne
  have key : ∀ f : G₂ → k, f g₂ = f g₂' := by
    intro f
    have h1 := funAlgEquivInducedMap_spec e g₂ (e.symm f)
    have h2 := funAlgEquivInducedMap_spec e g₂' (e.symm f)
    simp only [AlgEquiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, heq]
  have := key (Pi.single g₂ 1)
  simp [hne] at this

/-- Upgrade `funAlgEquivInducedMap` to a bijection `G₂ ≃ G₁` using injectivity of both
sides and finite cardinalities. -/
noncomputable def funAlgEquivInducedEquiv (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) : G₂ ≃ G₁ := by
  apply Equiv.ofBijective (funAlgEquivInducedMap e)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨funAlgEquivInducedMap_injective e, ?_⟩
  have h1 := Fintype.card_le_of_injective _ (funAlgEquivInducedMap_injective e)
  have h2 := Fintype.card_le_of_injective _ (funAlgEquivInducedMap_injective e.symm)
  omega

end FunAlgEquivEquiv

namespace Corollary1278

/-- For Hopf algebra equivalences `e₁ : H ≃ₐ (G₁ → k)` and `e₂ : H ≃ₐ (G₂ → k)`, the
induced point map `G₂ → G₁` from `e₁.symm.trans e₂` is a group homomorphism. -/
theorem funAlgEquivInducedMap_mul_of_hopf
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (G₁ : Type v) [Group G₁] [Fintype G₁] [DecidableEq G₁]
    (G₂ : Type v) [Group G₂] [Fintype G₂] [DecidableEq G₂]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [FiniteDimensional k H]
    (e₁ : H ≃ₐ[k] (G₁ → k)) (e₂ : H ≃ₐ[k] (G₂ → k))
    (a b : G₂) :
    funAlgEquivInducedMap (e₁.symm.trans e₂) (a * b) =
    funAlgEquivInducedMap (e₁.symm.trans e₂) a *
    funAlgEquivInducedMap (e₁.symm.trans e₂) b := by sorry

end Corollary1278

set_option maxHeartbeats 800000 in
/-- Corollary 1.27.8 (existence): every finite-dimensional commutative Hopf algebra over
an algebraically closed field of characteristic zero is isomorphic to the algebra of
functions `Fun(G, k)` on a finite group `G`. -/
theorem Corollary_1_27_8_comm_Hopf_is_Fun_G
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing H] [HopfAlgebra k H] [FiniteDimensional k H] :
    ∃ (G : Type v) (_ : Group G) (_ : Fintype G) (_ : DecidableEq G),
      Nonempty (H ≃ₐ[k] (G → k)) := by

  haveI hArt : IsArtinianRing H := isArtinian_of_tower k (inferInstance : IsArtinian k H)

  haveI hRed : IsReduced H := HopfAlgebra.commHopfAlgebra_isReduced k H

  haveI : Finite (MaximalSpectrum H) := inferInstance
  haveI hFintype : Fintype (MaximalSpectrum H) := Fintype.ofFinite _

  letI hGrp : Group (MaximalSpectrum H) :=
    Corollary1278.maximalSpectrumGroupOfHopfAlgebra k H

  haveI hDec : DecidableEq (MaximalSpectrum H) := Classical.decEq _

  refine ⟨MaximalSpectrum H, hGrp, hFintype, hDec, ⟨?_⟩⟩


  let e1 : H ≃ₐ[k] (∀ I : MaximalSpectrum H, H ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi H).restrictScalars k

  let e2 : (∀ I : MaximalSpectrum H, H ⧸ I.asIdeal) ≃ₐ[k] (MaximalSpectrum H → k) :=
    AlgEquiv.piCongrRight
      (fun I => (Corollary1278.residueFieldEquivOfAlgClosed k H I).symm)
  exact e1.trans e2

/-- Corollary 1.27.8 (uniqueness): the finite group `G` such that `H ≅ Fun(G, k)` is
unique up to group isomorphism. -/
theorem Corollary_1_27_8_comm_Hopf_unique_G
    (k : Type u)
    [Field k] [IsAlgClosed k] [CharZero k]
    (G₁ : Type v) [Group G₁] [Fintype G₁] [DecidableEq G₁]
    (G₂ : Type v) [Group G₂] [Fintype G₂] [DecidableEq G₂]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [FiniteDimensional k H]
    (e₁ : H ≃ₐ[k] (G₁ → k)) (e₂ : H ≃ₐ[k] (G₂ → k)) :
    Nonempty (G₁ ≃* G₂) := by

  let e := e₁.symm.trans e₂

  let φ := funAlgEquivInducedEquiv e

  have hmul : ∀ a b : G₂, φ.toFun (a * b) = φ.toFun a * φ.toFun b := by
    intro a b
    show funAlgEquivInducedMap e (a * b) =
      funAlgEquivInducedMap e a * funAlgEquivInducedMap e b
    exact Corollary1278.funAlgEquivInducedMap_mul_of_hopf k G₁ G₂ H e₁ e₂ a b

  exact ⟨(MulEquiv.mk φ hmul).symm⟩

namespace Corollary1278

/-- For a finite-dimensional commutative Hopf algebra `H ≅ Fun(G, k)`, the preimage of
each indicator function `δ_g` is a grouplike element of `H`. -/
theorem algEquiv_symm_piSingle_grouplike
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing H] [HopfAlgebra k H] [FiniteDimensional k H]
    (G : Type v) [Group G] [Fintype G] [DecidableEq G]
    (e : H ≃ₐ[k] (G → k))
    (g : G) :
    e.symm (Pi.single g (1 : k) : G → k) ∈ HopfAlgebra.grouplikeElements (R := k) (H := H) := by sorry

end Corollary1278

/-- In a finite-dimensional commutative Hopf algebra over an algebraically closed field of
characteristic zero, the grouplike elements span the whole algebra. -/
theorem commHopfAlgebra_grouplikeElements_span
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing H] [HopfAlgebra k H] [FiniteDimensional k H] :
    Submodule.span k (HopfAlgebra.grouplikeElements (R := k) (H := H)) = ⊤ := by

  obtain ⟨G, hGrp, hFin, hDec, ⟨e⟩⟩ := Corollary_1_27_8_comm_Hopf_is_Fun_G k H

  have hGL : ∀ g : G, e.symm (Pi.single g (1 : k) : G → k) ∈
      HopfAlgebra.grouplikeElements (R := k) (H := H) :=
    Corollary1278.algEquiv_symm_piSingle_grouplike k H G e

  rw [eq_top_iff]
  intro h _

  suffices h ∈ Submodule.span k
      (Set.range (fun g : G => e.symm (Pi.single g (1 : k) : G → k))) by
    exact Submodule.span_mono (Set.range_subset_iff.mpr (fun g => hGL g)) this

  have hkey : h = e.symm (e h) := (AlgEquiv.symm_apply_apply e h).symm
  rw [hkey]


  have hsum : (e h) = ∑ g : G, (e h g) • (Pi.single g (1 : k) : G → k) := by
    ext g'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  rw [hsum, map_sum]
  apply Submodule.sum_mem
  intro g _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- Lemma 1.33.2: in characteristic zero, every symmetric 2-cocycle on `S(V)` is a
2-coboundary. -/
theorem Lemma_1_33_2
    (k : Type u) (V : Type u) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V]
    (u : SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V)
    (hsymm : SymmetricAlgebra.IsSymmetricTensor k V u)
    (hcocycle : SymmetricAlgebra.IsCocycle2 k V u) :
    SymmetricAlgebra.IsCoboundary2 k V u :=
  SymmetricAlgebra.symmetric_cocycle_is_coboundary k V u hsymm hcocycle
