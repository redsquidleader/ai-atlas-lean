/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HopfAlgebra
import Atlas.TensorCategories.code.CoradicalFiltration
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Smooth.Basic

set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


/-- A coalgebra `(H, Δ, ε)` is cocommutative if the comultiplication is symmetric:
`τ ∘ Δ = Δ` for the flip `τ : H ⊗ H → H ⊗ H`. -/
class Coalgebra.IsCocommutative (R : Type u) (H : Type v)
    [CommSemiring R] [AddCommMonoid H] [Module R H] [Coalgebra R H] : Prop where
  cocomm : (TensorProduct.comm R H H).toLinearMap ∘ₗ (comul : H →ₗ[R] H ⊗[R] H) = comul

/-- Pointwise form of cocommutativity: `τ(Δ h) = Δ h` for every element `h`. -/
theorem cocommutative_comul_apply (R : Type u) (H : Type v)
    [CommSemiring R] [AddCommMonoid H] [Module R H] [Coalgebra R H]
    [Coalgebra.IsCocommutative R H] (h : H) :
    (TensorProduct.comm R H H) (comul (R := R) h) = comul h :=
  LinearMap.congr_fun Coalgebra.IsCocommutative.cocomm h


section PrimitiveElements

variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [Bialgebra R H]

/-- An element `x` of a bialgebra `H` is primitive if `Δ x = x ⊗ 1 + 1 ⊗ x`. -/
def HopfAlgebra.IsPrimitive (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ 1 + 1 ⊗ₜ x

/-- The submodule of primitive elements of a bialgebra `H` over `R`. -/
def HopfAlgebra.primitiveElements : Submodule R H where
  carrier := {x : H | HopfAlgebra.IsPrimitive (R := R) x}
  add_mem' {x y} (hx : HopfAlgebra.IsPrimitive x) (hy : HopfAlgebra.IsPrimitive y) := by
    show HopfAlgebra.IsPrimitive (R := R) (x + y)
    unfold HopfAlgebra.IsPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show HopfAlgebra.IsPrimitive (R := R) 0
    simp [HopfAlgebra.IsPrimitive, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x (hx : HopfAlgebra.IsPrimitive x) := by
    show HopfAlgebra.IsPrimitive (R := R) (r • x)
    unfold HopfAlgebra.IsPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

/-- Every primitive element has counit zero, i.e. lies in the augmentation ideal: the
image of `ε x ∈ R` in `H` vanishes. -/
theorem HopfAlgebra.IsPrimitive.algebraMap_counit_eq_zero
    {x : H} (hx : HopfAlgebra.IsPrimitive (R := R) x) :
    algebraMap R H (Coalgebra.counit (R := R) x) = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := R) x
  rw [hx] at h
  simp only [map_add, LinearMap.rTensor_tmul, Bialgebra.counit_one] at h
  have h2 := congr_arg (TensorProduct.lid R H) h
  simp only [map_add, TensorProduct.lid_tmul, one_smul] at h2
  rw [Algebra.algebraMap_eq_smul_one]
  have : counit (R := R) x • (1 : H) = 0 := by
    have := sub_eq_zero.mpr h2
    simp at this
    exact this
  exact this

/-- The Lie bracket of two primitive elements is primitive, so primitive elements form a
Lie subalgebra. -/
theorem HopfAlgebra.IsPrimitive.lie_bracket {x y : H}
    (hx : HopfAlgebra.IsPrimitive (R := R) x)
    (hy : HopfAlgebra.IsPrimitive (R := R) y) :
    HopfAlgebra.IsPrimitive (R := R) ⁅x, y⁆ := by
  rw [Ring.lie_def]
  unfold HopfAlgebra.IsPrimitive at *
  rw [map_sub, Bialgebra.comul_mul, Bialgebra.comul_mul, hx, hy]
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

/-- The commutator `xy - yx` of two primitive elements is primitive (`lie_bracket`
unfolded). -/
theorem HopfAlgebra.IsPrimitive.commutator {x y : H}
    (hx : HopfAlgebra.IsPrimitive (R := R) x)
    (hy : HopfAlgebra.IsPrimitive (R := R) y) :
    HopfAlgebra.IsPrimitive (R := R) (x * y - y * x) := by
  have := hx.lie_bracket hy
  rwa [Ring.lie_def] at this

end PrimitiveElements


section PrimitiveLieAlgebra

variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

/-- The Lie subalgebra `Prim(H)` of primitive elements of a Hopf algebra `H`, with bracket
inherited from the commutator. -/
def HopfAlgebra.primitiveLieSubalgebra : LieSubalgebra R H where
  toSubmodule := HopfAlgebra.primitiveElements (R := R)
  lie_mem' hx hy := HopfAlgebra.IsPrimitive.lie_bracket hx hy

/-- The canonical algebra map `U(Prim(H)) → H` from the universal enveloping algebra of
the Lie algebra of primitive elements into `H`. -/
noncomputable def HopfAlgebra.canonicalMapUEA :
    UniversalEnvelopingAlgebra R (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)) →ₐ[R] H :=
  (UniversalEnvelopingAlgebra.lift R) (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)).incl

end PrimitiveLieAlgebra


section UEARange

variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

/-- The range of `canonicalMapUEA` is contained in the subalgebra generated by primitive
elements. -/
theorem HopfAlgebra.canonicalMapUEA_range_le_adjoin :
    (HopfAlgebra.canonicalMapUEA (R := R) (H := H)).range ≤
      Algebra.adjoin R (HopfAlgebra.primitiveElements (R := R) (H := H) : Set H) := by
  intro x hx
  rw [AlgHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H))) y
  set g := (HopfAlgebra.canonicalMapUEA (R := R) (H := H)).comp
    (UniversalEnvelopingAlgebra.mkAlgHom R (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)))
  change g z ∈ _
  induction z using TensorAlgebra.induction with
  | algebraMap r =>
    simp only [g, AlgHom.commutes, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ r
  | ι m =>
    show g (TensorAlgebra.ι R m) ∈ _
    have : g (TensorAlgebra.ι R m) =
        (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)).incl m := by
      simp only [g, AlgHom.comp_apply, HopfAlgebra.canonicalMapUEA]
      exact congr_fun (UniversalEnvelopingAlgebra.ι_comp_lift R
        (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)).incl) m
    rw [this]
    exact Algebra.subset_adjoin m.property
  | mul a b ha hb =>
    show g (a * b) ∈ _; rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb =>
    show g (a + b) ∈ _; rw [map_add]; exact Subalgebra.add_mem _ ha hb

/-- If the canonical map `U(Prim(H)) → H` is surjective, then `H` is generated as an
algebra by its primitive elements. -/
theorem HopfAlgebra.surjective_canonicalMapUEA_adjoin_top
    (hsurj : Function.Surjective (HopfAlgebra.canonicalMapUEA (R := R) (H := H))) :
    Algebra.adjoin R (HopfAlgebra.primitiveElements (R := R) (H := H) : Set H) = ⊤ := by
  rw [eq_top_iff]; intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact HopfAlgebra.canonicalMapUEA_range_le_adjoin ⟨y, rfl⟩

/-- Every primitive element of `H` lies in the image of the canonical map
`U(Prim(H)) → H`. -/
theorem HopfAlgebra.primitiveElements_subset_range_canonicalMapUEA
    {k : Type u} {H : Type v} [CommRing k] [Ring H] [HopfAlgebra k H] :
    (HopfAlgebra.primitiveElements (R := k) (H := H) : Set H) ⊆
      ↑(HopfAlgebra.canonicalMapUEA (R := k) (H := H)).range := by
  intro x hx
  show x ∈ (HopfAlgebra.canonicalMapUEA (R := k) (H := H)).range
  rw [AlgHom.mem_range]
  exact ⟨UniversalEnvelopingAlgebra.ι k ⟨x, hx⟩, by
    have := congr_fun
      (UniversalEnvelopingAlgebra.ι_comp_lift k
        (HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H)).incl) ⟨x, hx⟩
    simp only [Function.comp_apply, HopfAlgebra.canonicalMapUEA] at this ⊢
    exact this⟩

/-- Converse to `surjective_canonicalMapUEA_adjoin_top`: if `H` is generated by its
primitive elements then the canonical map `U(Prim(H)) → H` is surjective. -/
theorem HopfAlgebra.surjective_of_primitives_generate
    {k : Type u} {H : Type v} [CommRing k] [Ring H] [HopfAlgebra k H]
    (hgen : Algebra.adjoin k
      ((HopfAlgebra.primitiveElements (R := k) (H := H) : Set H)) = ⊤) :
    Function.Surjective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) := by
  rw [← AlgHom.range_eq_top]
  rw [eq_top_iff, ← hgen]
  exact Algebra.adjoin_le
    HopfAlgebra.primitiveElements_subset_range_canonicalMapUEA

end UEARange


section GrouplikeElements

variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

/-- An element `g` of a Hopf algebra `H` is grouplike if `Δ g = g ⊗ g` and `ε g = 1`. -/
def HopfAlgebra.IsGrouplikeHopf (g : H) : Prop :=
  comul (R := R) g = g ⊗ₜ g ∧ counit (R := R) g = 1

/-- The set of grouplike elements of a Hopf algebra `H`. -/
def HopfAlgebra.grouplikeElements : Set H :=
  {g : H | HopfAlgebra.IsGrouplikeHopf (R := R) g}

/-- The product of two grouplike elements is grouplike. -/
theorem HopfAlgebra.IsGrouplikeHopf.mul {g h : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g)
    (hh : HopfAlgebra.IsGrouplikeHopf (R := R) h) :
    HopfAlgebra.IsGrouplikeHopf (R := R) (g * h) := by
  constructor
  · rw [Bialgebra.comul_mul, hg.1, hh.1]
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  · rw [Bialgebra.counit_mul, hg.2, hh.2, one_mul]

/-- The unit element `1 : H` is grouplike. -/
theorem HopfAlgebra.IsGrouplikeHopf.one :
    HopfAlgebra.IsGrouplikeHopf (R := R) (1 : H) := by
  constructor
  · rw [Bialgebra.comul_one]; simp [Algebra.TensorProduct.one_def]
  · exact Bialgebra.counit_one

/-- For a grouplike element `g`, the antipode is a two-sided inverse:
`g · S(g) = 1`. -/
theorem HopfAlgebra.IsGrouplikeHopf.mul_antipode {g : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
    g * antipode R g = 1 := by
  have := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) g
  rw [hg.1] at this
  simp [LinearMap.lTensor_tmul, LinearMap.mul'_apply,
        hg.2, Algebra.algebraMap_eq_smul_one] at this
  exact this

/-- For a grouplike element `g`, the antipode is a two-sided inverse:
`S(g) · g = 1`. -/
theorem HopfAlgebra.IsGrouplikeHopf.antipode_mul {g : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
    antipode R g * g = 1 := by
  have := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) g
  rw [hg.1] at this
  simp [LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        hg.2, Algebra.algebraMap_eq_smul_one] at this
  exact this

/-- Every grouplike element of a Hopf algebra over a nontrivial base ring is nonzero
(since `ε g = 1 ≠ 0`). -/
theorem HopfAlgebra.IsGrouplikeHopf.ne_zero [Nontrivial R] {g : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) : g ≠ 0 := by
  intro h
  have h2 := hg.2
  rw [h, map_zero] at h2
  exact zero_ne_one h2

/-- Promote a grouplike element to a unit of `H`, using the antipode as its inverse. -/
noncomputable def HopfAlgebra.IsGrouplikeHopf.toUnit {g : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) : Hˣ where
  val := g
  inv := antipode R g
  val_inv := hg.mul_antipode
  inv_val := hg.antipode_mul

/-- The counit of `S(g)` equals `1` for any grouplike `g`. -/
theorem HopfAlgebra.IsGrouplikeHopf.counit_antipode {g : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
    counit (R := R) (antipode R g) = 1 := by
  rw [HopfAlgebra.counit_antipode]
  exact hg.2

end GrouplikeElements


/-- Existence of the PBW filtration on `U(Prim(H))` compatible with the coradical
filtration of `H`: there is a monotone, exhaustive filtration `F : ℕ → Submodule k U` such
that `canonicalMapUEA` maps `F n` into the `n`-th piece of the coradical filtration. -/
theorem HopfAlgebra.pbwFiltration
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [Ring H] [HopfAlgebra k H]
    [Coalgebra.IsCocommutative k H]
    (hconn : HopfAlgebra.grouplikeElements (R := k) (H := H) = {1}) :
    ∃ F : ℕ → Submodule k (UniversalEnvelopingAlgebra k
        (HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H))),

      Monotone F ∧

      (⨆ n, F n = ⊤) ∧

      (∀ n x, x ∈ F n →
        (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) x ∈
          coradicalFiltration (R := k) (C := H) n) := by sorry


/-- Injectivity of the canonical map `U(Prim(H)) → H` in characteristic zero (a key step
in the Cartier–Kostant–Milnor–Moore theorem). -/
theorem HopfAlgebra.canonicalMapUEA_injective
    (k : Type u) (H : Type v)
    [Field k] [CharZero k]
    [Ring H] [HopfAlgebra k H] :
    Function.Injective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) := by sorry

/-- Strengthening of `pbwFiltration`: the PBW filtration is moreover strictly compatible
with the coradical filtration, i.e. the canonical map is injective layer-by-layer. -/
theorem HopfAlgebra.coradicalFiltration_compatible_injective
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [Ring H] [HopfAlgebra k H]
    [Coalgebra.IsCocommutative k H]
    (hconn : HopfAlgebra.grouplikeElements (R := k) (H := H) = {1}) :
    ∃ F : ℕ → Submodule k (UniversalEnvelopingAlgebra k
        (HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H))),

      Monotone F ∧

      (⨆ n, F n = ⊤) ∧

      (∀ n x, x ∈ F n →
        (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) x ∈
          coradicalFiltration (R := k) (C := H) n) ∧

      (∀ x, x ∈ F 0 →
        (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) x = 0 → x = 0) ∧


      (∀ n x, x ∈ F (n + 1) →
        (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) x = 0 → x ∈ F n) := by

  obtain ⟨F, hMono, hExhaust, hCompat⟩ := HopfAlgebra.pbwFiltration k H hconn

  have hInj := HopfAlgebra.canonicalMapUEA_injective k H
  refine ⟨F, hMono, hExhaust, hCompat, ?_, ?_⟩
  ·
    intro x _ hψx

    have h0 : (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) 0 = 0 := map_zero _
    exact hInj (hψx.trans h0.symm)
  ·
    intro n x _ hψx

    have h0 : (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) 0 = 0 := map_zero _
    have : x = 0 := hInj (hψx.trans h0.symm)
    rw [this]; exact (F n).zero_mem

section SymmetricCocycle

variable (k : Type u) (V : Type u) [Field k] [CharZero k] [AddCommGroup V] [Module k V]

local notation "SV" => SymmetricAlgebra k V

/-- The standard comultiplication on the symmetric algebra `S(V)` making it a bialgebra:
the generators are sent to primitives, `v ↦ v ⊗ 1 + 1 ⊗ v`. -/
noncomputable def SymmetricAlgebra.comul : SV →ₐ[k] SV ⊗[k] SV :=
  SymmetricAlgebra.lift
    (Algebra.TensorProduct.includeLeft.toLinearMap.comp (SymmetricAlgebra.ι k (M := V)) +
     Algebra.TensorProduct.includeRight.toLinearMap.comp (SymmetricAlgebra.ι k (M := V)))

/-- A 2-tensor `u ∈ S(V) ⊗ S(V)` is symmetric if it is fixed by the flip. -/
def SymmetricAlgebra.IsSymmetricTensor
    (u : SV ⊗[k] SV) : Prop :=
  (TensorProduct.comm k SV SV) u = u

/-- The cocycle condition for a 2-tensor `u ∈ S(V) ⊗ S(V)` with respect to the standard
comultiplication: `(Δ ⊗ 1) u + u ⊗ 1 = (1 ⊗ Δ) u + 1 ⊗ u` (up to the associator). -/
def SymmetricAlgebra.IsCocycle2
    (u : SV ⊗[k] SV) : Prop :=
  let Δ := (SymmetricAlgebra.comul k V).toLinearMap
  let assoc := (TensorProduct.assoc k SV SV SV)
  LinearMap.rTensor SV Δ u + u ⊗ₜ[k] 1 =
    assoc.symm (LinearMap.lTensor SV Δ u) + assoc.symm (1 ⊗ₜ[k] u)

/-- A 2-tensor `u` is a coboundary if it equals `Δ w - w ⊗ 1 - 1 ⊗ w` for some
`w ∈ S(V)`. -/
def SymmetricAlgebra.IsCoboundary2
    (u : SV ⊗[k] SV) : Prop :=
  ∃ w : SV,
    u = (SymmetricAlgebra.comul k V) w -
      (Algebra.TensorProduct.includeLeft : SV →ₐ[k] SV ⊗[k] SV) w -
      (Algebra.TensorProduct.includeRight : SV →ₐ[k] SV ⊗[k] SV) w

/-- The multiplication map `S(V) ⊗ S(V) → S(V)`, regarded as an algebra map (using
commutativity of `S(V)`). -/
noncomputable def SymmetricAlgebra.mulMap : SV ⊗[k] SV →ₐ[k] SV :=
  Algebra.TensorProduct.lmul' k

/-- The doubling algebra endomorphism of `S(V)` sending each generator `v` to `2v`. -/
noncomputable def SymmetricAlgebra.doubling : SV →ₐ[k] SV :=
  SymmetricAlgebra.lift (2 • SymmetricAlgebra.ι k (M := V))

/-- `mulMap ∘ comul` on `S(V)` equals the doubling endomorphism `v ↦ 2v`. -/
lemma SymmetricAlgebra.mulMap_comp_comul :
    (SymmetricAlgebra.mulMap k V).comp (SymmetricAlgebra.comul k V) =
    SymmetricAlgebra.doubling k V := by
  ext v
  show (mulMap k V) ((comul k V) (SymmetricAlgebra.ι k (M := V) v)) =
       (doubling k V) (SymmetricAlgebra.ι k (M := V) v)
  simp only [comul, SymmetricAlgebra.lift_ι_apply, LinearMap.add_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_add]
  rw [show (mulMap k V) (Algebra.TensorProduct.includeLeft (SymmetricAlgebra.ι k (M := V) v)) =
        SymmetricAlgebra.ι k (M := V) v from by simp [mulMap]]
  rw [show (mulMap k V) (Algebra.TensorProduct.includeRight (SymmetricAlgebra.ι k (M := V) v)) =
        SymmetricAlgebra.ι k (M := V) v from by simp [mulMap]]
  simp only [doubling, SymmetricAlgebra.lift_ι_apply, LinearMap.smul_apply]
  ring

/-- The multiplication map is a retraction of the left inclusion: `m(w ⊗ 1) = w`. -/
lemma SymmetricAlgebra.mulMap_includeLeft (w : SV) :
    SymmetricAlgebra.mulMap k V ((Algebra.TensorProduct.includeLeft : SV →ₐ[k] SV ⊗[k] SV) w) = w := by
  simp [SymmetricAlgebra.mulMap]

/-- The multiplication map is a retraction of the right inclusion: `m(1 ⊗ w) = w`. -/
lemma SymmetricAlgebra.mulMap_includeRight (w : SV) :
    SymmetricAlgebra.mulMap k V ((Algebra.TensorProduct.includeRight : SV →ₐ[k] SV ⊗[k] SV) w) = w := by
  simp [SymmetricAlgebra.mulMap]

/-- Computation of `mulMap` on a coboundary: `m(Δ w - w ⊗ 1 - 1 ⊗ w) = doubling(w) - 2w`. -/
lemma SymmetricAlgebra.mulMap_coboundary (w : SV) :
    SymmetricAlgebra.mulMap k V
      ((SymmetricAlgebra.comul k V) w -
       (Algebra.TensorProduct.includeLeft : SV →ₐ[k] SV ⊗[k] SV) w -
       (Algebra.TensorProduct.includeRight : SV →ₐ[k] SV ⊗[k] SV) w) =
    SymmetricAlgebra.doubling k V w - 2 * w := by
  have h1 : (SymmetricAlgebra.mulMap k V) ((SymmetricAlgebra.comul k V) w) =
      (SymmetricAlgebra.doubling k V) w := by
    rw [← AlgHom.comp_apply, SymmetricAlgebra.mulMap_comp_comul]
  simp only [map_sub, h1, SymmetricAlgebra.mulMap_includeLeft,
    SymmetricAlgebra.mulMap_includeRight]
  ring

end SymmetricCocycle

/-- In characteristic zero, every symmetric 2-cocycle on the symmetric coalgebra `S(V)` is
a coboundary. This is the analytic input to the Cartier–Kostant theorem. -/
theorem SymmetricAlgebra.symmetric_cocycle_is_coboundary
    (k : Type u) (V : Type u) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V]
    (u : SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V)
    (hsymm : SymmetricAlgebra.IsSymmetricTensor k V u)
    (hcocycle : SymmetricAlgebra.IsCocycle2 k V u) :
    SymmetricAlgebra.IsCoboundary2 k V u := by
  sorry

/-- Milnor–Moore (surjectivity part): over an algebraically closed field of characteristic
zero, the canonical map `U(Prim(H)) → H` is surjective whenever `H` is connected
cocommutative. -/
theorem HopfAlgebra.milnorMoore_surjective
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [Ring H] [HopfAlgebra k H]
    [Coalgebra.IsCocommutative k H]
    (hconn : HopfAlgebra.grouplikeElements (R := k) (H := H) = {1}) :
    Function.Surjective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) := by
  sorry

/-- Block decomposition: in a cocommutative Hopf algebra over an algebraically closed
field of characteristic zero, every element is a linear combination of products
`g · a` with `g` grouplike and `a` in the image of `U(Prim(H))`. -/
theorem HopfAlgebra.pointed_block_decomposition_span
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [Ring H] [HopfAlgebra k H]
    [Coalgebra.IsCocommutative k H] :
    ∀ h : H, h ∈ Submodule.span k
      { x : H | ∃ (g : H) (a : H),
        g ∈ HopfAlgebra.grouplikeElements (R := k) (H := H) ∧
        a ∈ Set.range (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) ∧
        x = g * a } := by
  sorry

/-- Corollary of the block decomposition: a cocommutative Hopf algebra over an
algebraically closed field of characteristic zero is generated as an algebra by its
grouplike elements together with the image of `U(Prim(H))`. -/
theorem HopfAlgebra.pointedCoalgebraDecomposition
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [Ring H] [HopfAlgebra k H]
    [Coalgebra.IsCocommutative k H] :
    Algebra.adjoin k
      (HopfAlgebra.grouplikeElements (R := k) (H := H) ∪
       Set.range (HopfAlgebra.canonicalMapUEA (R := k) (H := H))) = ⊤ := by
  rw [eq_top_iff]
  intro h _

  have hspan := HopfAlgebra.pointed_block_decomposition_span k H h

  set S := Algebra.adjoin k
    (HopfAlgebra.grouplikeElements (R := k) (H := H) ∪
     Set.range (HopfAlgebra.canonicalMapUEA (R := k) (H := H)))

  have hle : { x : H | ∃ (g : H) (a : H),
      g ∈ HopfAlgebra.grouplikeElements (R := k) (H := H) ∧
      a ∈ Set.range (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) ∧
      x = g * a } ⊆ (S.toSubmodule : Set H) := by
    intro x ⟨g, a, hg, ha, hx⟩
    rw [hx]
    show g * a ∈ S.toSubmodule
    rw [Subalgebra.mem_toSubmodule]
    exact Subalgebra.mul_mem S
      (Algebra.subset_adjoin (Set.mem_union_left _ hg))
      (Algebra.subset_adjoin (Set.mem_union_right _ ha))

  have hmem : h ∈ S.toSubmodule :=
    Submodule.span_le.mpr hle hspan
  rw [Subalgebra.mem_toSubmodule] at hmem
  exact hmem


section NilradicalHopfInfra

/-- The counit of a nilpotent element in a Hopf algebra is zero. -/
lemma HopfAlgebra.counit_nilpotent_eq_zero
    {k : Type u} {H : Type v}
    [Field k] [CommRing H] [HopfAlgebra k H]
    {x : H} (hx : IsNilpotent x) :
    Coalgebra.counit (R := k) x = 0 := by
  have h : IsNilpotent (Bialgebra.counitAlgHom k H x) := hx.map _
  rwa [isNilpotent_iff_eq_zero] at h

/-- The image of a nilpotent element under the antipode of a commutative Hopf algebra is
nilpotent. -/
lemma HopfAlgebra.antipode_isNilpotent_comm
    {k : Type u} {H : Type v}
    [Field k] [CommRing H] [HopfAlgebra k H]
    {x : H} (hx : IsNilpotent x) :
    IsNilpotent (HopfAlgebra.antipode k x) :=
  hx.map (HopfAlgebra.antipodeAlgHom (R := k) (A := H))

/-- Every nilpotent element of a commutative Hopf algebra lies in the kernel of the
counit. -/
lemma HopfAlgebra.nilpotent_mem_counit_ker
    {k : Type u} {H : Type v}
    [Field k] [CommRing H] [HopfAlgebra k H]
    {x : H} (hx : IsNilpotent x) :
    x ∈ RingHom.ker (Bialgebra.counitAlgHom k H) := by
  simp only [RingHom.mem_ker]
  exact HopfAlgebra.counit_nilpotent_eq_zero hx

/-- The comultiplication of a nilpotent element in a commutative Hopf algebra is again
nilpotent (as an element of `H ⊗ H`). -/
lemma HopfAlgebra.comul_isNilpotent
    {k : Type u} {H : Type v}
    [Field k] [CommRing H] [HopfAlgebra k H]
    {x : H} (hx : IsNilpotent x) :
    IsNilpotent (Coalgebra.comul (R := k) x) :=
  hx.map (Bialgebra.comulAlgHom k H)

/-- The nilradical of a commutative Hopf algebra is contained in the kernel of the
counit. -/
lemma HopfAlgebra.nilradical_le_counit_ker
    {k : Type u} {H : Type v}
    [Field k] [CommRing H] [HopfAlgebra k H] :
    nilradical H ≤ RingHom.ker (Bialgebra.counitAlgHom k H) := by
  intro x hx
  rw [mem_nilradical] at hx
  simp only [RingHom.mem_ker]
  have h : IsNilpotent (Bialgebra.counitAlgHom k H x) := hx.map _
  rwa [isNilpotent_iff_eq_zero] at h

end NilradicalHopfInfra

/-- A finitely generated subcoalgebra of a commutative Hopf algebra is contained in some
finitely generated Hopf subalgebra. -/
theorem HopfAlgebra.fg_subcoalgebra_generates_hopfSubalgebra
    (k : Type u) (H : Type v)
    [Field k] [CommRing H] [HopfAlgebra k H]
    (D : Submodule k H) (hD_sub : D.IsSubcoalgebra) (hD_fg : D.FG) :
    ∃ (S : Subalgebra k H) (_ : S.FG) (_ : HopfAlgebra k S),
      (D : Set H) ⊆ ↑S := by
  sorry

/-- Every element of a commutative Hopf algebra lies in a finitely generated Hopf
subalgebra. -/
theorem HopfAlgebra.element_mem_fg_hopfSubalgebra
    (k : Type u) (H : Type v)
    [Field k] [CommRing H] [HopfAlgebra k H]
    (x : H) :
    ∃ (S : Subalgebra k H) (_ : S.FG) (_ : HopfAlgebra k S),
      x ∈ S := by

  obtain ⟨D, hD_sub, hD_fg, hx_mem⟩ := exists_fg_subcoalgebra k H x

  obtain ⟨S, hS_fg, hS_hopf, hD_le_S⟩ :=
    HopfAlgebra.fg_subcoalgebra_generates_hopfSubalgebra k H D hD_sub hD_fg

  exact ⟨S, hS_fg, hS_hopf, hD_le_S hx_mem⟩

/-- Over an algebraically closed field of characteristic zero, every finitely generated
commutative Hopf algebra is formally smooth (Cartier's theorem). -/
theorem HopfAlgebra.formallySmooth_of_fg_commHopf_algClosed
    (k : Type u) (S : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing S] [Algebra k S] [HopfAlgebra k S] [Algebra.FiniteType k S] :
    Algebra.FormallySmooth k S := by


  sorry

/-- A finitely generated formally-smooth algebra over an algebraically closed field of
characteristic zero is reduced. -/
theorem Algebra.isReduced_of_formallySmooth_algClosed
    (k : Type u) (S : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [Algebra.FormallySmooth k S] :
    IsReduced S := by
  sorry

/-- Each finitely generated Hopf subalgebra of a commutative Hopf algebra (over an
algebraically closed field of characteristic zero) is reduced. -/
theorem HopfAlgebra.fg_hopfSubalgebra_isReduced_algClosed
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing H] [HopfAlgebra k H]
    (S : Subalgebra k H) (_hfg : S.FG) [HopfAlgebra k S] : IsReduced S := by
  haveI : Algebra.FiniteType k S := ⟨S.fg_top.mpr _hfg⟩
  haveI := HopfAlgebra.formallySmooth_of_fg_commHopf_algClosed k (↥S)
  exact Algebra.isReduced_of_formallySmooth_algClosed k (↥S)

/-- A commutative Hopf algebra over an algebraically closed field of characteristic zero
is reduced. -/
theorem HopfAlgebra.commHopfAlgebra_isReduced_algClosed
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing H] [HopfAlgebra k H] : IsReduced H := by
  constructor
  intro x hx

  obtain ⟨S, hSfg, hSHopf, hxS⟩ := HopfAlgebra.element_mem_fg_hopfSubalgebra k H x

  haveI : HopfAlgebra k S := hSHopf
  have hSred : IsReduced S :=
    HopfAlgebra.fg_hopfSubalgebra_isReduced_algClosed k H S hSfg

  have hx' : IsNilpotent (⟨x, hxS⟩ : S) := by
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

  exact congr_arg Subtype.val (hSred.eq_zero _ hx')

/-- Every finitely generated subalgebra of a commutative Hopf algebra in characteristic
zero is geometrically reduced. -/
theorem HopfAlgebra.commHopfAlgebra_fg_subalgebra_isGeometricallyReduced
    (k : Type u) (H : Type v)
    [Field k] [CharZero k]
    [CommRing H] [HopfAlgebra k H]
    (B : Subalgebra k H)
    (_hB : B.FG) :
    @Algebra.IsGeometricallyReduced k B _ B.toRing B.algebra := by
  rw [Algebra.isGeometricallyReduced_iff]
  have hH : IsReduced (TensorProduct k (AlgebraicClosure k) H) :=
    HopfAlgebra.commHopfAlgebra_isReduced_algClosed
      (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) H)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k (AlgebraicClosure k)) B.val)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)


section GrouplikeGroup

variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

/-- The set of grouplike elements of a Hopf algebra, packaged as a subtype to carry a
group structure. -/
def HopfAlgebra.GrouplikeGroup (R : Type u) (H : Type v)
    [CommRing R] [Ring H] [HopfAlgebra R H] : Type v :=
  { g : H // HopfAlgebra.IsGrouplikeHopf (R := R) g }

/-- The antipode of a grouplike element is grouplike for the comultiplication:
`Δ(S(g)) = S(g) ⊗ S(g)`. -/
theorem HopfAlgebra.comul_antipode_grouplike
    {R : Type u} {H : Type v} [CommRing R] [Ring H] [HopfAlgebra R H]
    {g : H} (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
    comul (R := R) (antipode R g) = (antipode R g) ⊗ₜ (antipode R g) := by sorry

/-- The antipode of a grouplike element is itself grouplike. -/
theorem HopfAlgebra.IsGrouplikeHopf.antipode_grouplike {g : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
    HopfAlgebra.IsGrouplikeHopf (R := R) (antipode R g) := by
  constructor
  · exact HopfAlgebra.comul_antipode_grouplike hg
  · exact hg.counit_antipode

/-- The grouplike elements of a Hopf algebra form a group under multiplication, with
inverse given by the antipode. -/
noncomputable instance HopfAlgebra.GrouplikeGroup.instGroup :
    Group (HopfAlgebra.GrouplikeGroup R H) where
  mul g h := ⟨g.1 * h.1, g.2.mul h.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one := ⟨1, HopfAlgebra.IsGrouplikeHopf.one⟩
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv g := ⟨antipode R g.1, g.2.antipode_grouplike⟩
  inv_mul_cancel g := Subtype.ext g.2.antipode_mul

/-- The natural monoid homomorphism `GrouplikeGroup R H →* H` extracting the underlying
element. -/
def HopfAlgebra.GrouplikeGroup.val : HopfAlgebra.GrouplikeGroup R H →* H where
  toFun g := g.1
  map_one' := rfl
  map_mul' _ _ := rfl

end GrouplikeGroup


/-- The smash product algebra `k[G] ⋉ U(𝔤)` of the group algebra of `G` and the universal
enveloping algebra of a Lie algebra `𝔤`, when `G` acts on `𝔤` by Lie automorphisms. -/
def SmashProductAlgebra (k : Type u) (G : Type u) (𝔤 : Type u)
    [Field k] [Group G] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [MulAction G 𝔤] : Type u := by sorry

/-- Ring instance on the smash product algebra. -/
def SmashProductAlgebra.instRing {k : Type u} {G : Type u} {𝔤 : Type u}
    [Field k] [Group G] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [MulAction G 𝔤] : Ring (SmashProductAlgebra k G 𝔤) := by sorry

/-- `k`-algebra instance on the smash product algebra. -/
def SmashProductAlgebra.instAlgebra {k : Type u} {G : Type u} {𝔤 : Type u}
    [Field k] [Group G] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [MulAction G 𝔤] : @Algebra k (SmashProductAlgebra k G 𝔤) _
      SmashProductAlgebra.instRing.toSemiring := by sorry

/-- Noncomputable `Ring` instance on the smash product algebra registered for typeclass
inference. -/
noncomputable instance SmashProductAlgebra.instRing'
    {k : Type u} {G : Type u} {𝔤 : Type u}
    [Field k] [Group G] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [MulAction G 𝔤] : Ring (SmashProductAlgebra k G 𝔤) :=
  SmashProductAlgebra.instRing

/-- Noncomputable `Algebra k` instance on the smash product algebra registered for
typeclass inference. -/
noncomputable instance SmashProductAlgebra.instAlgebra'
    {k : Type u} {G : Type u} {𝔤 : Type u}
    [Field k] [Group G] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [MulAction G 𝔤] : Algebra k (SmashProductAlgebra k G 𝔤) :=
  SmashProductAlgebra.instAlgebra


section SmashProductIso

variable (k : Type u) (H : Type v)
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocommutative k H]

/-- Conjugation action of the grouplike group of `H` on the Lie algebra `Prim(H)` of
primitive elements: `g · x := g x g^{-1}`. -/
def HopfAlgebra.grouplikeConjugationAction
    (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CharZero k]
    [Ring H] [HopfAlgebra k H]
    [Coalgebra.IsCocommutative k H] :
    MulAction (HopfAlgebra.GrouplikeGroup k H)
      (HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H)) := by sorry

/-- Cartier–Kostant theorem: a cocommutative Hopf algebra over an algebraically closed
field of characteristic zero is isomorphic to the smash product
`k[G(H)] ⋉ U(Prim(H))`. -/
theorem HopfAlgebra.cartierKostant_iso
    (k : Type u) (H : Type u)
    [Field k] [IsAlgClosed k] [CharZero k]
    [Ring H] [HopfAlgebra k H]
    [Coalgebra.IsCocommutative k H] :
    let G := HopfAlgebra.GrouplikeGroup k H
    let 𝔤 := HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H)
    let act := HopfAlgebra.grouplikeConjugationAction k H
    Nonempty (@AlgEquiv k
      (@SmashProductAlgebra k G 𝔤 _ _ _ _ act)
      H
      _
      (@SmashProductAlgebra.instRing k G 𝔤 _ _ _ _ act).toSemiring
      (inferInstance : Semiring H)
      (@SmashProductAlgebra.instAlgebra k G 𝔤 _ _ _ _ act)
      (inferInstance : Algebra k H)) :=
  sorry

end SmashProductIso
