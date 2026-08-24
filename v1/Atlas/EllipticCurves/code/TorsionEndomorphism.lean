/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Atlas.EllipticCurves.code.Isogenies

universe u

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- The multiplication-by-`n` endomorphism `[n]` on the group of points of a Weierstrass
curve, packaged as an additive group homomorphism `W.Point →+ W.Point`. -/
def multiplicationByN (W : WeierstrassCurve.Affine F) (n : ℤ) : W.Point →+ W.Point :=
  zsmulAddGroupHom n

/-- Evaluating the multiplication-by-`n` map at a point `P` is the same as the integer
scalar multiple `n • P`. -/
@[simp]
theorem multiplicationByN_apply (W : WeierstrassCurve.Affine F) (n : ℤ) (P : W.Point) :
    multiplicationByN W n P = n • P :=
  rfl

/-- The `n`-torsion subgroup `E[n]` of a Weierstrass curve, defined as the kernel of the
multiplication-by-`n` homomorphism. -/
def torsionSubgroup (W : WeierstrassCurve.Affine F) (n : ℤ) : AddSubgroup W.Point :=
  (multiplicationByN W n).ker

/-- A point `P` lies in `E[n]` if and only if `n • P = 0`. -/
@[simp]
theorem mem_torsionSubgroup (W : WeierstrassCurve.Affine F) (n : ℤ) (P : W.Point) :
    P ∈ torsionSubgroup W n ↔ n • P = 0 := by
  simp [torsionSubgroup, multiplicationByN, AddMonoidHom.mem_ker]

/-- Any additive group homomorphism between point groups of Weierstrass curves preserves
the `n`-torsion subgroup. -/
theorem map_mem_torsionSubgroup {W₁ W₂ : WeierstrassCurve.Affine F}
    (φ : W₁.Point →+ W₂.Point) (n : ℤ) (P : W₁.Point)
    (hP : P ∈ torsionSubgroup W₁ n) :
    φ P ∈ torsionSubgroup W₂ n := by
  simp only [mem_torsionSubgroup] at hP ⊢
  rw [← φ.map_zsmul, hP, map_zero]

/-- A Weierstrass curve `W` over a field of characteristic `p` is ordinary if its
`p`-torsion `E[p]` is isomorphic to `ℤ/pℤ` (cf. Definition 6.2 of Sutherland). -/
def IsOrdinary (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p] [Fact (Nat.Prime p)] :
    Prop :=
  Nonempty ((torsionSubgroup W (p : ℤ)) ≃+ ZMod p)

/-- A Weierstrass curve `W` over a field of characteristic `p` is supersingular if its
`p`-torsion `E[p]` is trivial (cf. Definition 6.2 of Sutherland). -/
def IsSupersingular (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p]
    [Fact (Nat.Prime p)] : Prop :=
  torsionSubgroup W (p : ℤ) = ⊥

/-- For a supersingular curve, any point killed by multiplication by `p` is the zero
point. -/
theorem IsSupersingular.torsion_eq_zero {W : WeierstrassCurve.Affine F}
    {p : ℕ} [CharP F p] [Fact (Nat.Prime p)]
    (h : IsSupersingular W p) (P : W.Point) (hP : (p : ℤ) • P = 0) : P = 0 := by
  have : P ∈ torsionSubgroup W (p : ℤ) := by simp [hP]
  rw [h] at this
  exact AddSubgroup.mem_bot.mp this

/-- A curve is supersingular if and only if multiplication by `p` is injective on its
group of points. -/
theorem isSupersingular_iff {W : WeierstrassCurve.Affine F}
    {p : ℕ} [CharP F p] [Fact (Nat.Prime p)] :
    IsSupersingular W p ↔ ∀ (P : W.Point), (p : ℤ) • P = 0 → P = 0 := by
  constructor
  · exact fun h P hP => h.torsion_eq_zero P hP
  · intro h
    rw [IsSupersingular, AddSubgroup.eq_bot_iff_forall]
    intro P hP
    exact h P (by rwa [mem_torsionSubgroup] at hP)

namespace Isogeny

variable {E₁ E₂ : WeierstrassCurve.Affine F}

end Isogeny

variable {E₁ E₂ : WeierstrassCurve.Affine F}

/-- Multiplication-by-`n` is natural with respect to additive group homomorphisms between
point groups: `[n] ∘ α = α ∘ [n]` (cf. Proposition 6.5 of Sutherland). -/
theorem multiplicationByN_comp_hom
    (α : E₁.Point →+ E₂.Point) (n : ℤ) :
    (multiplicationByN E₂ n).comp α = α.comp (multiplicationByN E₁ n) := by
  ext P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply]
  exact (α.map_zsmul P n).symm

/-- The pointwise version of `multiplicationByN_comp_hom`: `n • (α P) = α (n • P)`. -/
theorem multiplicationByN_comm_hom_apply
    (α : E₁.Point →+ E₂.Point) (n : ℤ) (P : E₁.Point) :
    n • (α P) = α (n • P) :=
  (α.map_zsmul P n).symm

/-- A nonzero integer multiple of a (nonzero) isogeny remains a nonzero homomorphism;
expresses the torsion-freeness of `Hom(E₁, E₂)` as a `ℤ`-module. -/
theorem Isogeny.zsmul_ne_zero
    {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (φ : Isogeny E₁ E₂) (n : ℤ) (hn : n ≠ 0) :
    n • φ.toAddMonoidHom ≠ 0 := by sorry

/-- The `ℤ`-module `Hom(E₁, E₂)` is torsion-free: if `n • α = 0` for some nonzero `n`,
then `α = 0`. -/
theorem hom_torsion_free
    {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : E₁.Point →+ E₂.Point) (n : ℤ) (hn : n ≠ 0)
    (h : n • α = 0) : α = 0 := by sorry

/-- The `ℤ`-rank of `Hom(E₁, E₂)` is at most 4, a classical structural fact for the
homomorphism group between two elliptic curves. -/
theorem hom_finrank_le_four
    {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F} :
    Module.finrank ℤ (E₁.Point →+ E₂.Point) ≤ 4 := by sorry

section Lemma66

variable {E₀ E₁ E₂ : WeierstrassCurve.Affine F}

/-- Right-cancellation for isogenies (one half of Lemma 6.6): if `α ∘ γ = β ∘ γ` with
`γ` an isogeny (hence surjective), then `α = β` as homomorphisms. -/
theorem Isogeny.right_cancel
    (α β : Isogeny E₁ E₂) (γ : Isogeny E₀ E₁)
    (h : α.toAddMonoidHom.comp γ.toAddMonoidHom = β.toAddMonoidHom.comp γ.toAddMonoidHom) :
    α.toAddMonoidHom = β.toAddMonoidHom := by
  ext Q
  obtain ⟨P, hP⟩ := γ.surjective Q
  have := DFunLike.congr_fun h P
  simp only [AddMonoidHom.comp_apply] at this
  rwa [hP] at this

/-- An isogeny composed with a nonzero homomorphism is itself nonzero: pre-composition by
an isogeny `δ` reflects nonzeroness of homomorphisms. -/
theorem Isogeny.comp_nonzero_of_nonzero
    {F : Type u} [Field F] [DecidableEq F]
    {E₀ E₁ E₂ : WeierstrassCurve.Affine F}
    (δ : Isogeny E₁ E₂) (f : E₀.Point →+ E₁.Point) (hf : f ≠ 0) :
    δ.toAddMonoidHom.comp f ≠ 0 := by sorry

/-- Left-cancellation for isogenies (the other half of Lemma 6.6): if `δ ∘ α = δ ∘ β`
with `δ` an isogeny, then `α = β` as homomorphisms. -/
theorem Isogeny.left_cancel
    (δ : Isogeny E₁ E₂) (α β : Isogeny E₀ E₁)
    (h : δ.toAddMonoidHom.comp α.toAddMonoidHom = δ.toAddMonoidHom.comp β.toAddMonoidHom) :
    α.toAddMonoidHom = β.toAddMonoidHom := by
  by_contra hne

  have hdiff : α.toAddMonoidHom - β.toAddMonoidHom ≠ 0 := by
    intro heq
    apply hne
    ext P
    have := DFunLike.congr_fun heq P
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this
    exact this

  have hcomp : δ.toAddMonoidHom.comp (α.toAddMonoidHom - β.toAddMonoidHom) = 0 := by
    ext P
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, map_sub,
               AddMonoidHom.zero_apply]
    have := DFunLike.congr_fun h P
    simp only [AddMonoidHom.comp_apply] at this
    exact sub_eq_zero.mpr this

  exact absurd hcomp (Isogeny.comp_nonzero_of_nonzero δ _ hdiff)

end Lemma66

end WeierstrassCurve.Affine

noncomputable section

open WeierstrassCurve

/-- The `n`-torsion subgroup `E(K)[n]` of an elliptic curve `E/k` after base change to a
field extension `K`, defined as the torsion subgroup of the projective point group. -/
def EllipticCurve.torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) : AddSubgroup (E.map (algebraMap k K)).toProjective.Point :=
  AddSubgroup.torsionBy (E.map (algebraMap k K)).toProjective.Point n

/-- Membership characterisation: a point `P ∈ E(K)` lies in `E(K)[n]` iff `n • P = 0`. -/
@[simp]
lemma EllipticCurve.mem_torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) (P : (E.map (algebraMap k K)).toProjective.Point) :
    P ∈ EllipticCurve.torsionSubgroup k E K n ↔ n • P = 0 := by
  simp [EllipticCurve.torsionSubgroup]

/-- Over an algebraically closed field `K`, when `n` is coprime to the characteristic,
the `n`-torsion `E(K)[n]` is finite — a Fintype instance underlying Theorem 6.1. -/
noncomputable def EllipticCurve.torsionSubgroup_fintype
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime n (ringChar k)) :
    Fintype ↥(EllipticCurve.torsionSubgroup k E K (n : ℤ)) := by sorry

/-- Theorem 6.1 (cardinality part): over an algebraically closed field `K`, if `n` is
coprime to `char k`, then `#E(K)[n] = n²`. -/
theorem EllipticCurve.torsionSubgroup_card
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime n (ringChar k)) :
    @Fintype.card _ (EllipticCurve.torsionSubgroup_fintype k E K n hn hcop) = n ^ 2 := by sorry

/-- A finite abelian group of order `n²` whose every element is killed by `n` is
isomorphic to `(ℤ/nℤ)²`. Used as a structural step toward Theorem 6.1. -/
theorem addCommGroup_sq_card_killed_by_equiv_prod
    (G : Type*) [AddCommGroup G] [Fintype G]
    (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card G = n ^ 2)
    (hkill : ∀ x : G, n • x = 0) :
    Nonempty (G ≃+ ZMod n × ZMod n) := by sorry

/-- Theorem 6.1 (structure part): over an algebraically closed `K`, when `n` is coprime
to `char k`, the `n`-torsion is `E(K)[n] ≃ ℤ/nℤ ⊕ ℤ/nℤ`. -/
theorem EllipticCurve.torsion_equiv_zmod_prod
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime n (ringChar k)) :
    Nonempty (↥(EllipticCurve.torsionSubgroup k E K (n : ℤ)) ≃+ ZMod n × ZMod n) := by

  let hfin := EllipticCurve.torsionSubgroup_fintype k E K n hn hcop

  have hcard := EllipticCurve.torsionSubgroup_card k E K n hn hcop

  have hkill : ∀ x : ↥(EllipticCurve.torsionSubgroup k E K (n : ℤ)), n • x = 0 := by
    intro ⟨P, hP⟩
    rw [EllipticCurve.mem_torsionSubgroup] at hP
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_nsmul, AddSubgroup.coe_zero]

    change (n : ℤ) • P = 0 at hP
    rw [natCast_zsmul] at hP
    exact hP

  exact addCommGroup_sq_card_killed_by_equiv_prod _ n hn hcard hkill

/-- Theorem 6.1 (characteristic-`p` part): over an alg. closed `K`, the `p`-torsion is
either `ℤ/pℤ` (ordinary case) or trivial (supersingular case). -/
theorem EllipticCurve.torsion_p_dichotomy
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (p : ℕ) [CharP k p] [Fact (Nat.Prime p)] :
    Nonempty (↥(EllipticCurve.torsionSubgroup k E K (p : ℤ)) ≃+ ZMod p) ∨
    EllipticCurve.torsionSubgroup k E K (p : ℤ) = ⊥ := by sorry

/-- Over an algebraically closed field, multiplication-by-`n` (for `n ≠ 0`) is surjective
on the group of points of an elliptic curve. -/
theorem EllipticCurve.mulByInt_surjective
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (fun P : (E.map (algebraMap k K)).toProjective.Point => n • P) := by sorry

/-- Supersingularity is preserved under powers of `p`: if `E[p] = 0` then `E[pᵉ] = 0`
for all `e ≥ 1`. -/
theorem EllipticCurve.torsion_prime_char_supersingular
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (p : ℕ) [CharP k p] [Fact (Nat.Prime p)]
    (e : ℕ) (he : 0 < e)
    (hss : EllipticCurve.torsionSubgroup k E K (p : ℤ) = ⊥) :
    EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ e) = ⊥ := by

  induction e with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    ·
      subst hn
      simpa [pow_one] using hss
    ·
      have ih' : EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ n) = ⊥ :=
        ih (Nat.pos_of_ne_zero hn)
      rw [AddSubgroup.eq_bot_iff_forall]
      intro P hP
      rw [EllipticCurve.mem_torsionSubgroup] at hP


      have hpP_mem : (p : ℤ) • P ∈ EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ n) := by
        rw [EllipticCurve.mem_torsionSubgroup, ← mul_smul]


        rw [show (p : ℤ) ^ n * (p : ℤ) = (p : ℤ) ^ (n + 1) from by ring]
        exact hP
      rw [ih'] at hpP_mem
      rw [AddSubgroup.mem_bot] at hpP_mem

      have hP_mem : P ∈ EllipticCurve.torsionSubgroup k E K (p : ℤ) := by
        rw [EllipticCurve.mem_torsionSubgroup]
        exact hpP_mem
      rw [hss] at hP_mem
      exact AddSubgroup.mem_bot.mp hP_mem

/-- Ordinarity propagates to powers of `p`: if `E[p] ≃ ℤ/pℤ` then `E[pᵉ] ≃ ℤ/pᵉℤ`. -/
theorem EllipticCurve.torsion_prime_char_ordinary
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (p : ℕ) [CharP k p] [Fact (Nat.Prime p)]
    (e : ℕ) (he : 0 < e)
    (hord : Nonempty (↥(EllipticCurve.torsionSubgroup k E K (p : ℤ)) ≃+ ZMod p)) :
    Nonempty (↥(EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ e)) ≃+ ZMod (p ^ e)) := by sorry

/-- Corollary 6.4 (subgroup form): any finite subgroup of `E(K̄)` is a direct sum of (at
most) two cyclic groups, only one of which can have order divisible by `char k`. -/
theorem EllipticCurve.finite_subgroup_two_cyclic
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (T : AddSubgroup (E.map (algebraMap k K)).toProjective.Point) [Fintype T] :
    ∃ m₁ m₂ : ℕ, 0 < m₁ ∧ 0 < m₂ ∧ m₁ ∣ m₂ ∧
      Nonempty (T ≃+ ZMod m₁ × ZMod m₂) ∧
      (¬ (ringChar k ∣ m₁) ∨ ¬ (ringChar k ∣ m₂)) := by sorry

/-- Corollary 6.4 (finite field form): for `E/𝔽_q` of characteristic `p`,
`E(𝔽_q) ≃ ℤ/n₁ℤ ⊕ ℤ/n₂ℤ` with `n₂ ∣ n₁` and `p ∤ n₂`. -/
theorem EllipticCurve.finite_field_group_structure
    (k : Type*) [Field k] [Fintype k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    [Fintype E.toProjective.Point]
    (p : ℕ) [CharP k p] [Fact (Nat.Prime p)] :
    ∃ n₂ n₁ : ℕ, 0 < n₂ ∧ 0 < n₁ ∧ n₂ ∣ n₁ ∧ ¬(p ∣ n₂) ∧
      Nonempty (E.toProjective.Point ≃+ ZMod n₁ × ZMod n₂) := by sorry

end

section Theorem67

open WeierstrassCurve.Affine in
/-- The degree of a composition of isogenies is the product of the degrees:
`deg(ψ ∘ φ) = deg ψ · deg φ`. -/
@[simp] theorem Isogeny.degree_comp {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
    (ψ : Isogeny E₂ E₃) (φ : Isogeny E₁ E₂) :
    (Isogeny.comp ψ φ).degree = ψ.degree * φ.degree := rfl

/-- Two isogenies with the same underlying additive map must have the same degree (since
the degree is determined by the kernel/map data). -/
theorem Isogeny.degree_eq_of_toAddMonoidHom_eq {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α β : Isogeny E₁ E₂)
    (h : α.toAddMonoidHom = β.toAddMonoidHom) :
    α.degree = β.degree := by sorry

open WeierstrassCurve.Affine in
/-- The kernel of an isogeny `α` is contained in the kernel of multiplication-by-`deg α`;
this is a key step toward the construction of the dual isogeny (Theorem 6.7). -/
theorem Isogeny.kernel_le_torsion {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    α.toAddMonoidHom.ker ≤ (WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ)).ker := by sorry

/-- A degree-`1` isogeny has trivial kernel. -/
theorem Isogeny.ker_eq_bot_of_degree_one {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : α.degree = 1) :
    α.toAddMonoidHom.ker = ⊥ := by
  apply le_bot_iff.mp
  calc α.toAddMonoidHom.ker
      ≤ (WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ)).ker :=
          α.kernel_le_torsion
    _ = ⊥ := by
          ext P
          simp only [AddMonoidHom.mem_ker, WeierstrassCurve.Affine.multiplicationByN_apply,
            hdeg, Nat.cast_one, one_zsmul, AddSubgroup.mem_bot]

/-- A degree-`1` isogeny is injective on points. -/
theorem Isogeny.injective_of_degree_one {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : α.degree = 1) :
    Function.Injective α.toAddMonoidHom :=
  (AddMonoidHom.ker_eq_bot_iff α.toAddMonoidHom).mp (α.ker_eq_bot_of_degree_one hdeg)

open WeierstrassCurve.Affine in
/-- Existence of the dual for a degree-`1` isogeny: a degree-`1` isogeny is an isomorphism
and its inverse plays the role of the dual (cf. Theorem 6.7). -/
theorem Isogeny.dual_exists_degree_one {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : α.degree = 1) :
    ∃ (αd : Isogeny E₂ E₁),
      αd.toAddMonoidHom.comp α.toAddMonoidHom =
        WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) := by

  have hinj := α.injective_of_degree_one hdeg
  have hbij : Function.Bijective α.toAddMonoidHom := ⟨hinj, α.surjective⟩

  let e : E₁.Point ≃+ E₂.Point := AddEquiv.ofBijective α.toAddMonoidHom hbij

  let αd_hom : E₂.Point →+ E₁.Point := e.symm.toAddMonoidHom

  have αd_surj : Function.Surjective αd_hom := EquivLike.surjective e.symm


  refine ⟨⟨αd_hom, αd_surj, 1, Nat.one_pos⟩, ?_⟩


  ext P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply, hdeg]
  show e.symm (α.toAddMonoidHom P) = (1 : ℤ) • P
  rw [one_zsmul]
  exact e.symm_apply_apply P

/-- If `p` is a prime dividing the degree of an isogeny `α : E₁ → E₂` of degree `> 1`,
then there exists an intermediate curve and a degree-`p` quotient isogeny `β : E₁ → E_mid`
whose kernel is contained in that of `α`. -/
theorem Isogeny.exists_quotient_of_prime_dividing_degree
    {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : 1 < α.degree)
    (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ α.degree) :
    ∃ (E_mid : WeierstrassCurve.Affine F) (β : Isogeny E₁ E_mid),
      β.degree = p ∧ β.toAddMonoidHom.ker ≤ α.toAddMonoidHom.ker := by sorry

/-- For any prime divisor `p` of `deg α` (with `deg α > 1`), one can factor `α = γ ∘ β`
with `deg β = p` and the degrees multiplying to `deg α`. -/
theorem Isogeny.prime_factor_aux {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : 1 < α.degree)
    (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ α.degree) :
    ∃ (E_mid : WeierstrassCurve.Affine F)
      (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂),
      β.degree = p ∧
      0 < γ.degree ∧
      γ.degree * β.degree = α.degree ∧
      γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom := by

  obtain ⟨E_mid, β, hβ_deg, hker⟩ :=
    Isogeny.exists_quotient_of_prime_dividing_degree α hdeg p hp hdvd


  let γ_hom : E_mid.Point →+ E₂.Point :=
    β.toAddMonoidHom.liftOfSurjective β.surjective ⟨α.toAddMonoidHom, hker⟩
  have hγ_comp : γ_hom.comp β.toAddMonoidHom = α.toAddMonoidHom := by
    simp [γ_hom]


  have hγ_surj : Function.Surjective γ_hom := by
    intro z
    obtain ⟨x, hx⟩ := α.surjective z
    exact ⟨β.toAddMonoidHom x, by simp [γ_hom, hx]⟩

  have hγ_deg_pos : 0 < α.degree / p :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
  let γ : Isogeny E_mid E₂ := ⟨γ_hom, hγ_surj, α.degree / p, hγ_deg_pos⟩

  refine ⟨E_mid, β, γ, hβ_deg, hγ_deg_pos, ?_, hγ_comp⟩

  change α.degree / p * β.degree = α.degree
  rw [hβ_deg]
  exact Nat.div_mul_cancel hdvd

open WeierstrassCurve.Affine in
/-- A composite-degree isogeny can be properly factored: if `deg α > 1` is not prime, then
`α = γ ∘ β` with both `β` and `γ` of degree strictly less than `deg α`. -/
theorem Isogeny.factor_prime {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : 1 < α.degree) (hcomp : ¬ Nat.Prime α.degree) :
    ∃ (E_mid : WeierstrassCurve.Affine F)
      (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂),
      0 < β.degree ∧
      0 < γ.degree ∧
      γ.degree * β.degree = α.degree ∧
      γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom ∧
      β.degree < α.degree ∧
      γ.degree < α.degree := by

  have hne : α.degree ≠ 1 := by omega
  have ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne

  have hp_lt : p < α.degree := by
    have hle : p ≤ α.degree := Nat.le_of_dvd (by omega) hpd
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hp) hcomp


  obtain ⟨E_mid, β, γ, hβ_deg, hγ_pos, hcomp_deg, hcomp_eq⟩ :=
    Isogeny.prime_factor_aux α hdeg p hp hpd
  refine ⟨E_mid, β, γ, ?_, hγ_pos, hcomp_deg, hcomp_eq, ?_, ?_⟩
  ·
    rw [hβ_deg]; exact hp.pos
  ·
    rw [hβ_deg]; exact hp_lt
  ·
    have hprod : γ.degree * p = α.degree := by rw [← hβ_deg]; exact hcomp_deg
    have hp2 := hp.one_lt
    nlinarith

set_option maxHeartbeats 800000 in
open WeierstrassCurve.Affine in
/-- Existence of the dual via composition: if `α` factors as `γ ∘ β` with duals existing
for both `β` and `γ`, then a dual exists for `α` (used in the inductive proof of 6.7). -/
theorem Isogeny.dual_exists_of_comp {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ E_mid : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂)
    (hcomp : γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom)
    (hdeg : γ.degree * β.degree = α.degree)
    (hβ_dual : ∃ (βd : Isogeny E_mid E₁),
      βd.toAddMonoidHom.comp β.toAddMonoidHom =
        multiplicationByN E₁ (β.degree : ℤ))
    (hγ_dual : ∃ (γd : Isogeny E₂ E_mid),
      γd.toAddMonoidHom.comp γ.toAddMonoidHom =
        multiplicationByN E_mid (γ.degree : ℤ)) :
    ∃ (αd : Isogeny E₂ E₁),
      αd.toAddMonoidHom.comp α.toAddMonoidHom =
        multiplicationByN E₁ (α.degree : ℤ) := by
  obtain ⟨βd, hβd⟩ := hβ_dual
  obtain ⟨γd, hγd⟩ := hγ_dual

  refine ⟨Isogeny.comp βd γd, ?_⟩


  have key : ∀ P : E₁.Point,
      βd.toAddMonoidHom (γd.toAddMonoidHom (γ.toAddMonoidHom (β.toAddMonoidHom P))) =
        (↑α.degree : ℤ) • P := by
    intro P

    have h1 : γd.toAddMonoidHom (γ.toAddMonoidHom (β.toAddMonoidHom P)) =
        (γ.degree : ℤ) • (β.toAddMonoidHom P) := by
      have := DFunLike.congr_fun hγd (β.toAddMonoidHom P)
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
      exact this
    rw [h1]

    rw [map_zsmul βd.toAddMonoidHom]

    have h2 : βd.toAddMonoidHom (β.toAddMonoidHom P) = (β.degree : ℤ) • P := by
      have := DFunLike.congr_fun hβd P
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
      exact this
    rw [h2, ← mul_smul]
    congr 1
    exact_mod_cast hdeg

  ext P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply]


  have hαP : α.toAddMonoidHom P = γ.toAddMonoidHom (β.toAddMonoidHom P) := by
    have := DFunLike.congr_fun hcomp P
    simp only [AddMonoidHom.comp_apply] at this
    exact this.symm


  show βd.toAddMonoidHom (γd.toAddMonoidHom (α.toAddMonoidHom P)) = _
  rw [hαP]
  exact key P

/-- Multiplication-by-`n` is surjective on the points of a Weierstrass curve when
`n ≠ 0`. -/
theorem WeierstrassCurve.Affine.multiplicationByN_surjective
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (WeierstrassCurve.Affine.multiplicationByN E n) := by sorry

/-- Package multiplication-by-`n` as an `Isogeny E E` of degree `n²`. -/
noncomputable def Isogeny.multiplicationByN_isogeny {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) (n : ℤ) (hn : n ≠ 0) :
    Isogeny E E where
  toAddMonoidHom := WeierstrassCurve.Affine.multiplicationByN E n
  surjective := WeierstrassCurve.Affine.multiplicationByN_surjective E n hn
  degree := n.natAbs ^ 2
  degree_pos := by positivity

/-- The underlying additive homomorphism of the packaged multiplication-by-`n` isogeny is
exactly `multiplicationByN E n`. -/
theorem Isogeny.multiplicationByN_isogeny_toAddMonoidHom
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) (n : ℤ) (hn : n ≠ 0) :
    (Isogeny.multiplicationByN_isogeny E n hn).toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E n :=
  rfl

open WeierstrassCurve.Affine in
/-- Any self-isogeny whose underlying map is `multiplicationByN E n` has degree `n²`. -/
theorem Isogeny.degree_multiplicationByN {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (φ : Isogeny E E)
    (n : ℤ) (hn : n ≠ 0)
    (h : φ.toAddMonoidHom = WeierstrassCurve.Affine.multiplicationByN E n) :
    φ.degree = (n.natAbs) ^ 2 :=
  Isogeny.degree_eq_of_toAddMonoidHom_eq φ (Isogeny.multiplicationByN_isogeny E n hn)
    (h.trans (Isogeny.multiplicationByN_isogeny_toAddMonoidHom E n hn).symm)

open WeierstrassCurve.Affine in
/-- Factoring through the kernel: if `ker φ ⊆ ker ψ`, then `ψ` factors as `λ ∘ φ` for
some isogeny `λ` (existence statement). -/
theorem Isogeny.factor_through_kernel {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
    (φ : Isogeny E₁ E₂) (ψ : Isogeny E₁ E₃)
    (hker : φ.toAddMonoidHom.ker ≤ ψ.toAddMonoidHom.ker) :
    ∃ (lam : Isogeny E₂ E₃),
      lam.toAddMonoidHom.comp φ.toAddMonoidHom = ψ.toAddMonoidHom := by


  let lamHom : E₂.Point →+ E₃.Point :=
    φ.toAddMonoidHom.liftOfSurjective φ.surjective ⟨ψ.toAddMonoidHom, hker⟩
  have hcomp : lamHom.comp φ.toAddMonoidHom = ψ.toAddMonoidHom := by simp [lamHom]

  have hlam_surj : Function.Surjective lamHom := by
    intro z
    obtain ⟨x, hx⟩ := ψ.surjective z
    exact ⟨φ.toAddMonoidHom x, by simp [lamHom, hx]⟩

  exact ⟨⟨lamHom, hlam_surj, ψ.degree, ψ.degree_pos⟩, hcomp⟩

open WeierstrassCurve.Affine in
/-- Existence of the dual for a prime-degree isogeny: when `deg α` is prime, the dual
exists, by factoring `[deg α]` through `α`. -/
theorem Isogeny.dual_exists_prime_degree {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hp : Nat.Prime α.degree) :
    ∃ (αd : Isogeny E₂ E₁),
      αd.toAddMonoidHom.comp α.toAddMonoidHom =
        WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) := by

  have hℓ_ne_zero : (α.degree : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let mulℓ := Isogeny.multiplicationByN_isogeny E₁ (α.degree : ℤ) hℓ_ne_zero
  have hmul_hom : mulℓ.toAddMonoidHom = multiplicationByN E₁ (α.degree : ℤ) :=
    Isogeny.multiplicationByN_isogeny_toAddMonoidHom E₁ (α.degree : ℤ) hℓ_ne_zero

  have hker : α.toAddMonoidHom.ker ≤ mulℓ.toAddMonoidHom.ker := by
    rw [hmul_hom]; exact α.kernel_le_torsion


  obtain ⟨αd, hαd⟩ := Isogeny.factor_through_kernel α mulℓ hker
  exact ⟨αd, by rw [hαd, hmul_hom]⟩

open WeierstrassCurve.Affine in
/-- Theorem 6.7 (existence): for every isogeny `α : E₁ → E₂` there exists an isogeny
`α̂ : E₂ → E₁` satisfying `α̂ ∘ α = [deg α]`. Proven by strong induction on degree. -/
theorem Isogeny.dual_exists {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    ∃ (αd : Isogeny E₂ E₁),
      αd.toAddMonoidHom.comp α.toAddMonoidHom =
        WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) := by

  suffices ∀ (d : ℕ) {E₁ E₂ : WeierstrassCurve.Affine F} (α : Isogeny E₁ E₂),
      α.degree = d →
      ∃ (αd : Isogeny E₂ E₁),
        αd.toAddMonoidHom.comp α.toAddMonoidHom =
          multiplicationByN E₁ (α.degree : ℤ) by
    exact this α.degree α rfl
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro E₁' E₂' α' hαd
  by_cases hd1 : d ≤ 1
  ·
    have hpos := α'.degree_pos
    have hdeg1 : α'.degree = 1 := by omega
    exact Isogeny.dual_exists_degree_one α' hdeg1
  ·
    push_neg at hd1
    have hα_gt1 : 1 < α'.degree := by omega
    by_cases hprime : Nat.Prime α'.degree
    ·
      exact Isogeny.dual_exists_prime_degree α' hprime
    ·
      obtain ⟨E_mid, β, γ, hβ_pos, hγ_pos, hcomp_deg, hcomp_eq, hβ_lt, hγ_lt⟩ :=
        Isogeny.factor_prime α' hα_gt1 hprime

      have hβ_dual := ih β.degree (by omega) β rfl
      have hγ_dual := ih γ.degree (by omega) γ rfl

      exact Isogeny.dual_exists_of_comp α' β γ hcomp_eq hcomp_deg hβ_dual hγ_dual

end Theorem67

open WeierstrassCurve.Affine in
/-- Uniqueness of the dual at the homomorphism level (cf. Theorem 6.7): any two isogenies
`αd₁, αd₂` satisfying the defining equation of the dual agree as homomorphisms. -/
theorem Isogeny.dual_unique {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂)
    (αd₁ αd₂ : Isogeny E₂ E₁)
    (h₁ : αd₁.toAddMonoidHom.comp α.toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ))
    (h₂ : αd₂.toAddMonoidHom.comp α.toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ)) :
    αd₁.toAddMonoidHom = αd₂.toAddMonoidHom :=
  WeierstrassCurve.Affine.Isogeny.right_cancel αd₁ αd₂ α (h₁.trans h₂.symm)

open WeierstrassCurve.Affine in
/-- Theorem 6.7 in existence-and-uniqueness form: there is a unique-up-to-`toAddMonoidHom`
isogeny `α̂` satisfying `α̂ ∘ α = [deg α]`. -/
theorem Isogeny.dual_exists_unique {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    ∃ (αd : Isogeny E₂ E₁),
      αd.toAddMonoidHom.comp α.toAddMonoidHom =
        WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) ∧
      ∀ (β : Isogeny E₂ E₁),
        β.toAddMonoidHom.comp α.toAddMonoidHom =
          WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) →
        β.toAddMonoidHom = αd.toAddMonoidHom := by
  obtain ⟨αd, hαd⟩ := α.dual_exists
  exact ⟨αd, hαd, fun β hβ => α.dual_unique β αd hβ hαd⟩

/-- Extensionality for `Isogeny`: two isogenies are equal if their underlying homs and
degrees agree. -/
@[ext]
theorem Isogeny.ext {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    {α β : Isogeny E₁ E₂}
    (h_hom : α.toAddMonoidHom = β.toAddMonoidHom)
    (h_deg : α.degree = β.degree) :
    α = β := by
  cases α; cases β
  simp only [Isogeny.mk.injEq]
  exact ⟨h_hom, h_deg⟩

/-- Any isogeny `β` satisfying the dual equation `β ∘ α = [deg α]` automatically has
`deg β = deg α` — using `deg(β ∘ α) = (deg α)²`. -/
theorem Isogeny.degree_of_dual_property {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (β : Isogeny E₂ E₁)
    (hβ : β.toAddMonoidHom.comp α.toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ)) :
    β.degree = α.degree := by
  have hn : (α.degree : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp α.degree_pos)

  have hcomp_hom : (Isogeny.comp β α).toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) := hβ

  have hcomp_deg := Isogeny.degree_multiplicationByN (Isogeny.comp β α)
    (α.degree : ℤ) hn hcomp_hom


  have hnatabs : (α.degree : ℤ).natAbs = α.degree := Int.natAbs_natCast α.degree

  have hmul : β.degree * α.degree = α.degree ^ 2 := by
    have h1 : (Isogeny.comp β α).degree = β.degree * α.degree := rfl
    rw [h1] at hcomp_deg
    rw [hcomp_deg, hnatabs]

  have hpos := α.degree_pos
  have hne : α.degree ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  calc β.degree = β.degree * α.degree / α.degree := by rw [Nat.mul_div_cancel _ hpos]
    _ = α.degree ^ 2 / α.degree := by rw [hmul]
    _ = α.degree := by rw [Nat.pow_two]; exact Nat.mul_div_cancel _ hpos

/-- Definition 6.8: the dual isogeny `α̂` of `α`, obtained by choosing a witness from
`α.dual_exists`. -/
noncomputable def Isogeny.dualIsogeny {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) : Isogeny E₂ E₁ :=
  α.dual_exists.choose

open WeierstrassCurve.Affine in
/-- Defining property of the dual isogeny (Definition 6.8): `α̂ ∘ α = [deg α]`. -/
theorem Isogeny.dualIsogeny_comp {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    α.dualIsogeny.toAddMonoidHom.comp α.toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) :=
  α.dual_exists.choose_spec

open WeierstrassCurve.Affine in
/-- Pointwise form of `Isogeny.dualIsogeny_comp`: `α̂(α(P)) = (deg α) • P`. -/
theorem Isogeny.dualIsogeny_comp_apply {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (P : E₁.Point) :
    α.dualIsogeny (α P) = (α.degree : ℤ) • P := by
  have h := α.dualIsogeny_comp
  have := DFunLike.congr_fun h P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
  exact this

open WeierstrassCurve.Affine in
/-- Uniqueness of the dual at the homomorphism level: any `β : E₂ → E₁` with
`β ∘ α = [deg α]` agrees as a hom with `α.dualIsogeny`. -/
theorem Isogeny.dualIsogeny_unique {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (β : Isogeny E₂ E₁)
    (hβ : β.toAddMonoidHom.comp α.toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ)) :
    β.toAddMonoidHom = α.dualIsogeny.toAddMonoidHom :=
  α.dual_unique β α.dualIsogeny hβ α.dualIsogeny_comp

section Lemma610

open WeierstrassCurve.Affine

/-- The dual isogeny has the same degree as the original (part of Lemma 6.10). -/
theorem Isogeny.degree_dualIsogeny {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    α.dualIsogeny.degree = α.degree :=
  α.degree_of_dual_property α.dualIsogeny α.dualIsogeny_comp

open WeierstrassCurve.Affine in
/-- Strengthened existence-and-uniqueness of the dual as an `Isogeny` (not just at the
`toAddMonoidHom` level), using `Isogeny.ext` and `degree_dualIsogeny`. -/
theorem Isogeny.dual_exists_unique_isogeny {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    ∃ (αd : Isogeny E₂ E₁),
      αd.toAddMonoidHom.comp α.toAddMonoidHom =
        WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) ∧
      ∀ (β : Isogeny E₂ E₁),
        β.toAddMonoidHom.comp α.toAddMonoidHom =
          WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ) →
        β = αd := by
  refine ⟨α.dualIsogeny, α.dualIsogeny_comp, fun β hβ => ?_⟩
  exact Isogeny.ext
    (α.dualIsogeny_unique β hβ)
    ((α.degree_of_dual_property β hβ).trans α.degree_dualIsogeny.symm)

/-- The other half of Lemma 6.10: `α ∘ α̂ = [deg α]` on `E₂`, obtained by right-cancelling
through `α`. -/
theorem Isogeny.comp_dualIsogeny {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    α.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom =
      multiplicationByN E₂ (α.degree : ℤ) := by


  have hassoc : (α.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom).comp α.toAddMonoidHom =
      α.toAddMonoidHom.comp (α.dualIsogeny.toAddMonoidHom.comp α.toAddMonoidHom) := by
    ext P; simp only [AddMonoidHom.comp_apply]

  have hdual : α.dualIsogeny.toAddMonoidHom.comp α.toAddMonoidHom =
      multiplicationByN E₁ (α.degree : ℤ) :=
    α.dualIsogeny_comp

  have hcomm : α.toAddMonoidHom.comp (multiplicationByN E₁ (α.degree : ℤ)) =
      (multiplicationByN E₂ (α.degree : ℤ)).comp α.toAddMonoidHom :=
    (multiplicationByN_comp_hom α.toAddMonoidHom (α.degree : ℤ)).symm

  have hkey : (α.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom).comp α.toAddMonoidHom =
      (multiplicationByN E₂ (α.degree : ℤ)).comp α.toAddMonoidHom := by
    rw [hassoc, hdual, hcomm]

  let compIsog : Isogeny E₂ E₂ := Isogeny.comp α α.dualIsogeny
  have hcomp_hom : compIsog.toAddMonoidHom =
      α.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom := rfl

  have hn : (α.degree : ℤ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp α.degree_pos
  let mulN : Isogeny E₂ E₂ := Isogeny.multiplicationByN_isogeny E₂ (α.degree : ℤ) hn
  have hmulN_hom : mulN.toAddMonoidHom = multiplicationByN E₂ (α.degree : ℤ) :=
    Isogeny.multiplicationByN_isogeny_toAddMonoidHom E₂ (α.degree : ℤ) hn

  have hcancel : compIsog.toAddMonoidHom.comp α.toAddMonoidHom =
      mulN.toAddMonoidHom.comp α.toAddMonoidHom := by
    rw [hcomp_hom, hmulN_hom]; exact hkey
  have heq := Isogeny.right_cancel compIsog mulN α hcancel
  rw [hcomp_hom, hmulN_hom] at heq
  exact heq

/-- Pointwise form of `α ∘ α̂ = [deg α]`: `α(α̂(Q)) = (deg α) • Q`. -/
theorem Isogeny.comp_dualIsogeny_apply {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (Q : E₂.Point) :
    α (α.dualIsogeny Q) = (α.degree : ℤ) • Q := by
  have h := α.comp_dualIsogeny
  have := DFunLike.congr_fun h Q
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
  exact this

/-- The dual of the dual recovers the original (`α̂̂ = α`, part of Lemma 6.10). -/
theorem Isogeny.dualIsogeny_dualIsogeny {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) :
    α.dualIsogeny.dualIsogeny.toAddMonoidHom = α.toAddMonoidHom := by

  have h : α.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom =
      multiplicationByN E₂ (α.dualIsogeny.degree : ℤ) := by
    rw [Isogeny.degree_dualIsogeny]
    exact α.comp_dualIsogeny

  exact (α.dualIsogeny.dualIsogeny_unique α h).symm

/-- Lemma 6.10 (self-duality of `[n]`): for any `n ≠ 0`, `[n]̂ = [n]` as endomorphisms. -/
theorem Isogeny.multiplicationByN_self_dual {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) (n : ℤ) (hn : n ≠ 0) :
    (Isogeny.multiplicationByN_isogeny E n hn).dualIsogeny.toAddMonoidHom =
      multiplicationByN E n := by
  let mulN := Isogeny.multiplicationByN_isogeny E n hn
  have hmulN : mulN.toAddMonoidHom = multiplicationByN E n :=
    Isogeny.multiplicationByN_isogeny_toAddMonoidHom E n hn

  have hnn : (multiplicationByN E n).comp (multiplicationByN E n) =
      multiplicationByN E (n * n) := by
    ext P
    simp only [AddMonoidHom.comp_apply, multiplicationByN_apply, mul_smul]

  have hdeg : mulN.degree = n.natAbs ^ 2 :=
    Isogeny.degree_multiplicationByN mulN n hn hmulN

  have hcast : (mulN.degree : ℤ) = n * n := by
    rw [hdeg]
    push_cast
    rw [sq_abs]
    ring

  have hself : mulN.toAddMonoidHom.comp mulN.toAddMonoidHom =
      multiplicationByN E (mulN.degree : ℤ) := by
    rw [hmulN, hnn, hcast]

  have := mulN.dualIsogeny_unique mulN hself
  rw [hmulN] at this
  exact this.symm

end Lemma610

section Lemma611

open WeierstrassCurve.Affine

/-- Lemma 6.11: the dual is additive — `(α + β)̂ = α̂ + β̂` for `α, β ∈ Hom(E₁, E₂)`. -/
theorem Isogeny.dualIsogeny_add {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α β γ : Isogeny E₁ E₂)
    (hγ : γ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom) :
    γ.dualIsogeny.toAddMonoidHom =
      α.dualIsogeny.toAddMonoidHom + β.dualIsogeny.toAddMonoidHom := by sorry

/-- Pointwise form of Lemma 6.11 (`dualIsogeny_add`). -/
theorem Isogeny.dualIsogeny_add_apply {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α β γ : Isogeny E₁ E₂)
    (hγ : γ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom)
    (P : E₂.Point) :
    γ.dualIsogeny P = α.dualIsogeny P + β.dualIsogeny P := by
  have h := Isogeny.dualIsogeny_add α β γ hγ
  exact DFunLike.congr_fun h P

end Lemma611

section Lemma612

open WeierstrassCurve.Affine

/-- Lemma 6.12: the dual of a composition is the reversed composition of duals,
`(α ∘ β)̂ = β̂ ∘ α̂`. -/
theorem Isogeny.dualIsogeny_comp_eq {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
    (α : Isogeny E₂ E₃) (β : Isogeny E₁ E₂) :
    (Isogeny.comp α β).dualIsogeny.toAddMonoidHom =
      (Isogeny.comp β.dualIsogeny α.dualIsogeny).toAddMonoidHom := by


  let αβ := Isogeny.comp α β
  let βdαd := Isogeny.comp β.dualIsogeny α.dualIsogeny

  have hdef : βdαd.toAddMonoidHom.comp αβ.toAddMonoidHom =
      multiplicationByN E₁ (αβ.degree : ℤ) := by

    have hαβ_hom : αβ.toAddMonoidHom = α.toAddMonoidHom.comp β.toAddMonoidHom := rfl
    have hβdαd_hom : βdαd.toAddMonoidHom =
        β.dualIsogeny.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom := rfl


    have hassoc : βdαd.toAddMonoidHom.comp αβ.toAddMonoidHom =
        β.dualIsogeny.toAddMonoidHom.comp
          ((α.dualIsogeny.toAddMonoidHom.comp α.toAddMonoidHom).comp β.toAddMonoidHom) := by
      ext P; simp only [AddMonoidHom.comp_apply, hαβ_hom, hβdαd_hom]

    have hdualα : α.dualIsogeny.toAddMonoidHom.comp α.toAddMonoidHom =
        multiplicationByN E₂ (α.degree : ℤ) :=
      α.dualIsogeny_comp


    have hcomm : β.dualIsogeny.toAddMonoidHom.comp (multiplicationByN E₂ (α.degree : ℤ)) =
        (multiplicationByN E₁ (α.degree : ℤ)).comp β.dualIsogeny.toAddMonoidHom :=
      (multiplicationByN_comp_hom β.dualIsogeny.toAddMonoidHom (α.degree : ℤ)).symm

    have hdualβ : β.dualIsogeny.toAddMonoidHom.comp β.toAddMonoidHom =
        multiplicationByN E₁ (β.degree : ℤ) :=
      β.dualIsogeny_comp

    have hmulcomp : (multiplicationByN E₁ (α.degree : ℤ)).comp
        (multiplicationByN E₁ (β.degree : ℤ)) =
        multiplicationByN E₁ ((α.degree : ℤ) * (β.degree : ℤ)) := by
      ext P
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply, mul_smul]

    have hdeg : αβ.degree = α.degree * β.degree :=
      Isogeny.degree_comp α β

    rw [hassoc, hdualα]


    have step3 : β.dualIsogeny.toAddMonoidHom.comp
        ((multiplicationByN E₂ (↑α.degree : ℤ)).comp β.toAddMonoidHom) =
        (multiplicationByN E₁ (↑α.degree : ℤ)).comp
          (β.dualIsogeny.toAddMonoidHom.comp β.toAddMonoidHom) := by
      ext P
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply]
      rw [multiplicationByN_comm_hom_apply β.dualIsogeny.toAddMonoidHom]
    rw [step3, hdualβ, hmulcomp]


    congr 1

  exact (αβ.dualIsogeny_unique βdαd hdef).symm

end Lemma612

section Definition613

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)

/-- Definition 6.13: the endomorphism ring `End(E) = Hom(E, E)` as the additive monoid of
endomorphisms of `E.Point`, with multiplication given by composition. -/
abbrev EndRing : Type u :=
  AddMonoid.End E.Point

/-- Ring structure on `EndRing E`, inherited from `AddMonoid.End`. -/
instance : Ring (EndRing E) := AddMonoid.End.instRing

variable {E}

/-- The canonical ring homomorphism `ℤ → End(E)` sending `n` to `[n]`. -/
noncomputable def intToEndRingHom : ℤ →+* EndRing E :=
  Int.castRingHom (EndRing E)

/-- Evaluating `intToEndRingHom n` at a point `P` yields `n • P`. -/
@[simp]
theorem intToEndRingHom_apply (n : ℤ) (P : E.Point) :
    (intToEndRingHom (E := E) n) P = n • P := by
  simp [intToEndRingHom]

/-- The image of `n` under `intToEndRingHom` is the `multiplicationByN` endomorphism. -/
theorem intToEndRingHom_eq_multiplicationByN (n : ℤ) :
    intToEndRingHom (E := E) n = multiplicationByN E n :=
  rfl

/-- Integers (viewed as endomorphisms via `[n]`) commute with every endomorphism of `E`,
i.e. `[n]` lies in the center of `End(E)`. -/
theorem intCast_comm_endomorphism (n : ℤ) (α : EndRing E) :
    (n : EndRing E) * α = α * (n : EndRing E) := by
  apply AddMonoidHom.ext
  intro P
  show (n : EndRing E) (α P) = α ((n : EndRing E) P)
  simp only [AddMonoid.End.intCast_def]
  exact (α.map_zsmul P n).symm

/-- The product in `EndRing E` is composition pointwise: `(α * β) P = α (β P)`. -/
@[simp]
theorem EndRing.mul_apply' (α β : EndRing E) (P : E.Point) :
    (α * β) P = α (β P) := rfl

/-- The sum in `EndRing E` is pointwise addition. -/
@[simp]
theorem EndRing.add_apply' (α β : EndRing E) (P : E.Point) :
    (α + β) P = α P + β P := rfl

/-- The unit `1 : EndRing E` is the identity endomorphism. -/
@[simp]
theorem EndRing.one_apply' (P : E.Point) :
    (1 : EndRing E) P = P := rfl

/-- The zero `0 : EndRing E` sends every point to the zero point. -/
@[simp]
theorem EndRing.zero_apply' (P : E.Point) :
    (0 : EndRing E) P = 0 := rfl

end Definition613

section Lemma616

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- Auxiliary form of Lemma 6.16: if `oneMinusAlpha = [1] - α` as homs, then its dual
equals `[1] - α̂`. Used to relate the duals of `α` and `1 - α`. -/
theorem Isogeny.dualIsogeny_one_sub
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (h : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) :
    oneMinusAlpha.dualIsogeny.toAddMonoidHom =
      multiplicationByN E 1 - α.dualIsogeny.toAddMonoidHom := by

  let negOne := Isogeny.multiplicationByN_isogeny E (-1) (by omega)
  have hNegOne : negOne.toAddMonoidHom = multiplicationByN E (-1) :=
    Isogeny.multiplicationByN_isogeny_toAddMonoidHom E (-1) (by omega)
  have hNegOneDual : negOne.dualIsogeny.toAddMonoidHom = multiplicationByN E (-1) :=
    Isogeny.multiplicationByN_self_dual E (-1) (by omega)
  let negα := Isogeny.comp negOne α

  have hNegαHom : negα.toAddMonoidHom = -α.toAddMonoidHom := by
    ext P
    simp only [negα, Isogeny.comp, AddMonoidHom.neg_apply]
    change negOne.toAddMonoidHom (α.toAddMonoidHom P) = -α.toAddMonoidHom P
    rw [hNegOne]; simp [multiplicationByN_apply]

  let mul1 := Isogeny.multiplicationByN_isogeny E 1 (by omega)
  have hMul1 : mul1.toAddMonoidHom = multiplicationByN E 1 :=
    Isogeny.multiplicationByN_isogeny_toAddMonoidHom E 1 (by omega)

  have hSum : oneMinusAlpha.toAddMonoidHom = mul1.toAddMonoidHom + negα.toAddMonoidHom := by
    rw [hMul1, hNegαHom, h]
    ext P; simp [AddMonoidHom.add_apply, AddMonoidHom.neg_apply, sub_eq_add_neg]

  have hDualAdd := Isogeny.dualIsogeny_add mul1 negα oneMinusAlpha hSum
  rw [hDualAdd]

  have hMul1Dual : mul1.dualIsogeny.toAddMonoidHom = multiplicationByN E 1 :=
    Isogeny.multiplicationByN_self_dual E 1 (by omega)
  rw [hMul1Dual]

  have hNegαDual := Isogeny.dualIsogeny_comp_eq negOne α
  rw [hNegαDual]

  ext P
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.add_apply]
  change multiplicationByN E 1 P +
    Isogeny.comp (Isogeny.dualIsogeny α) (Isogeny.dualIsogeny negOne) P =
    multiplicationByN E 1 P - α.dualIsogeny.toAddMonoidHom P
  simp only [Isogeny.comp]
  change multiplicationByN E 1 P +
    α.dualIsogeny.toAddMonoidHom (negOne.dualIsogeny.toAddMonoidHom P) =
    multiplicationByN E 1 P - α.dualIsogeny.toAddMonoidHom P
  rw [show negOne.dualIsogeny.toAddMonoidHom P = (-1 : ℤ) • P from by
    have := DFunLike.congr_fun hNegOneDual P
    simp [multiplicationByN_apply] at this; exact this]
  congr 1
  rw [map_zsmul]
  simp

/-- Lemma 6.16: `α + α̂ = [1 + deg α - deg(1 - α)]` as endomorphisms of `E`. -/
theorem Isogeny.toAddMonoidHom_add_dualIsogeny
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (h_oma : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) :
    α.toAddMonoidHom + α.dualIsogeny.toAddMonoidHom =
      multiplicationByN E (1 + (α.degree : ℤ) - (oneMinusAlpha.degree : ℤ)) := by
  ext P
  simp only [AddMonoidHom.add_apply, multiplicationByN_apply]

  have hdual_oma_P :=
    DFunLike.congr_fun (oneMinusAlpha.dualIsogeny_comp) P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at hdual_oma_P

  have h_oma_P : oneMinusAlpha.toAddMonoidHom P = P - α.toAddMonoidHom P := by
    have := DFunLike.congr_fun h_oma P
    simp only [AddMonoidHom.sub_apply, multiplicationByN_apply, one_smul] at this
    exact this

  have hdual_form := Isogeny.dualIsogeny_one_sub α oneMinusAlpha h_oma
  have hdual_form_Q : ∀ Q : E.Point,
      oneMinusAlpha.dualIsogeny.toAddMonoidHom Q =
        Q - α.dualIsogeny.toAddMonoidHom Q := by
    intro Q
    have := DFunLike.congr_fun hdual_form Q
    simp only [AddMonoidHom.sub_apply, multiplicationByN_apply, one_smul] at this
    exact this

  have hdual_alpha_P : α.dualIsogeny.toAddMonoidHom (α.toAddMonoidHom P) =
      (α.degree : ℤ) • P := α.dualIsogeny_comp_apply P

  rw [h_oma_P] at hdual_oma_P
  rw [map_sub oneMinusAlpha.dualIsogeny.toAddMonoidHom] at hdual_oma_P
  rw [hdual_form_Q P, hdual_form_Q (α.toAddMonoidHom P)] at hdual_oma_P
  rw [hdual_alpha_P] at hdual_oma_P


  suffices h : α.toAddMonoidHom P + α.dualIsogeny.toAddMonoidHom P +
      (oneMinusAlpha.degree : ℤ) • P = (1 : ℤ) • P + (α.degree : ℤ) • P by
    have hsub := sub_eq_of_eq_add h.symm
    rw [hsub.symm]
    rw [← add_smul (1 : ℤ) (α.degree : ℤ) P, ← sub_smul]
  rw [one_smul]
  have := hdual_oma_P
  rw [show (oneMinusAlpha.degree : ℤ) • P =
    P - α.dualIsogeny.toAddMonoidHom P - (α.toAddMonoidHom P - (α.degree : ℤ) • P)
    from this.symm]
  abel

end Lemma616

section Definition617

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- Existence of an isogeny representing `[1] - α`, used to package the trace
construction underlying Definition 6.17. -/
theorem Isogeny.oneMinusAlpha_isogeny
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E) :
    ∃ (oma : Isogeny E E),
      oma.toAddMonoidHom = multiplicationByN E 1 - α.toAddMonoidHom := by sorry

/-- Auxiliary trace formula `tr α = 1 + deg α - deg(1 - α)` parameterised by a specific
witness of `1 - α` (cf. Definition 6.17). -/
noncomputable def Isogeny.traceAux
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (_ : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) : ℤ :=
  1 + (α.degree : ℤ) - (oneMinusAlpha.degree : ℤ)

/-- Rephrasing of Lemma 6.16 in terms of `traceAux`: `α + α̂ = [traceAux α (1-α)]`. -/
theorem Isogeny.toAddMonoidHom_add_dualIsogeny_eq_traceAux
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (h_oma : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) :
    α.toAddMonoidHom + α.dualIsogeny.toAddMonoidHom =
      multiplicationByN E (α.traceAux oneMinusAlpha h_oma) := by
  unfold Isogeny.traceAux
  exact α.toAddMonoidHom_add_dualIsogeny oneMinusAlpha h_oma

/-- Definition 6.17: the trace of an endomorphism `α`, defined via the integer such that
`α + α̂ = [tr α]`. Implemented by choosing a witness for `1 - α`. -/
noncomputable def Isogeny.trace
    (α : Isogeny E E) : ℤ :=
  α.traceAux α.oneMinusAlpha_isogeny.choose α.oneMinusAlpha_isogeny.choose_spec

/-- Defining identity for the trace (Definition 6.17): `α + α̂ = [tr α]`. -/
theorem Isogeny.toAddMonoidHom_add_dualIsogeny_eq_trace
    (α : Isogeny E E) :
    α.toAddMonoidHom + α.dualIsogeny.toAddMonoidHom =
      multiplicationByN E α.trace := by
  unfold Isogeny.trace
  exact α.toAddMonoidHom_add_dualIsogeny_eq_traceAux
    α.oneMinusAlpha_isogeny.choose
    α.oneMinusAlpha_isogeny.choose_spec

/-- Pointwise form of the trace identity: `α(P) + α̂(P) = (tr α) • P`. -/
theorem Isogeny.trace_apply
    (α : Isogeny E E)
    (P : E.Point) :
    α.toAddMonoidHom P + α.dualIsogeny.toAddMonoidHom P =
      α.trace • P := by
  have h := α.toAddMonoidHom_add_dualIsogeny_eq_trace
  have := DFunLike.congr_fun h P
  simp only [AddMonoidHom.add_apply, multiplicationByN_apply] at this
  exact this

end Definition617

section Theorem618

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- Convenience abbreviation `trace'` for `Isogeny.trace`, used to state Theorem 6.18. -/
noncomputable abbrev Isogeny.trace' {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F} (α : Isogeny E E) : ℤ := α.trace

/-- Trace identity restated using `trace'`: `α + α̂ = [trace' α]`. -/
theorem Isogeny.toAddMonoidHom_add_dualIsogeny_eq_trace'
    (α : Isogeny E E) :
    α.toAddMonoidHom + α.dualIsogeny.toAddMonoidHom =
      multiplicationByN E α.trace' :=
  α.toAddMonoidHom_add_dualIsogeny_eq_trace

/-- Combined existence statement: a witness `oma` of `1 - α` exists together with the
trace identity expressed via `1 + deg α - deg(oma)`. -/
theorem Isogeny.exists_oneMinusAlpha_add_dualIsogeny
    (α : Isogeny E E) :
    ∃ (oma : Isogeny E E),
      oma.toAddMonoidHom = multiplicationByN E 1 - α.toAddMonoidHom ∧
      α.toAddMonoidHom + α.dualIsogeny.toAddMonoidHom =
        multiplicationByN E (1 + (α.degree : ℤ) - (oma.degree : ℤ)) := by
  obtain ⟨oma, homa⟩ := α.oneMinusAlpha_isogeny
  exact ⟨oma, homa, α.toAddMonoidHom_add_dualIsogeny oma homa⟩

/-- Auxiliary form of Theorem 6.18 (characteristic polynomial via `traceAux`):
`α² - [tr α] α + [deg α] = 0` in `End(E)`. -/
theorem Isogeny.char_poly_alpha_aux
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (h_oma : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) :
    α.toAddMonoidHom.comp α.toAddMonoidHom -
      (multiplicationByN E (α.traceAux oneMinusAlpha h_oma)).comp α.toAddMonoidHom +
      multiplicationByN E (α.degree : ℤ) = 0 := by
  have htrace := α.toAddMonoidHom_add_dualIsogeny_eq_traceAux oneMinusAlpha h_oma
  have hdual := α.dualIsogeny_comp
  ext P
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.add_apply,
             multiplicationByN_apply, AddMonoidHom.zero_apply]
  have h_tr_apply : (α.traceAux oneMinusAlpha h_oma) • (α.toAddMonoidHom P) =
      α.toAddMonoidHom (α.toAddMonoidHom P) +
        α.dualIsogeny.toAddMonoidHom (α.toAddMonoidHom P) := by
    have := DFunLike.congr_fun htrace (α.toAddMonoidHom P)
    simp only [AddMonoidHom.add_apply, multiplicationByN_apply] at this
    exact this.symm
  have h_dual_apply : α.dualIsogeny.toAddMonoidHom (α.toAddMonoidHom P) =
      (α.degree : ℤ) • P :=
    α.dualIsogeny_comp_apply P
  rw [h_tr_apply, h_dual_apply]
  abel

/-- Theorem 6.18 (for `α`): `α` satisfies its characteristic equation
`α² - [tr α] α + [deg α] = 0`. -/
theorem Isogeny.char_poly_alpha
    (α : Isogeny E E) :
    α.toAddMonoidHom.comp α.toAddMonoidHom -
      (multiplicationByN E α.trace).comp α.toAddMonoidHom +
      multiplicationByN E (α.degree : ℤ) = 0 := by
  have htrace := α.toAddMonoidHom_add_dualIsogeny_eq_trace
  have hdual := α.dualIsogeny_comp
  ext P
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.add_apply,
             multiplicationByN_apply, AddMonoidHom.zero_apply]
  have h_tr_apply : α.trace • (α.toAddMonoidHom P) =
      α.toAddMonoidHom (α.toAddMonoidHom P) +
        α.dualIsogeny.toAddMonoidHom (α.toAddMonoidHom P) := by
    have := DFunLike.congr_fun htrace (α.toAddMonoidHom P)
    simp only [AddMonoidHom.add_apply, multiplicationByN_apply] at this
    exact this.symm
  have h_dual_apply : α.dualIsogeny.toAddMonoidHom (α.toAddMonoidHom P) =
      (α.degree : ℤ) • P :=
    α.dualIsogeny_comp_apply P
  rw [h_tr_apply, h_dual_apply]
  abel

/-- Auxiliary form of Theorem 6.18 for the dual: `α̂` also satisfies the same
characteristic equation, expressed via `traceAux`. -/
theorem Isogeny.char_poly_dualIsogeny_aux
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (h_oma : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) :
    α.dualIsogeny.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom -
      (multiplicationByN E (α.traceAux oneMinusAlpha h_oma)).comp
        α.dualIsogeny.toAddMonoidHom +
      multiplicationByN E (α.degree : ℤ) = 0 := by
  have htrace := α.toAddMonoidHom_add_dualIsogeny_eq_traceAux oneMinusAlpha h_oma
  have hcomp_dual := α.comp_dualIsogeny
  ext P
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.add_apply,
             multiplicationByN_apply, AddMonoidHom.zero_apply]
  have h_tr_apply : (α.traceAux oneMinusAlpha h_oma) •
      (α.dualIsogeny.toAddMonoidHom P) =
      α.toAddMonoidHom (α.dualIsogeny.toAddMonoidHom P) +
        α.dualIsogeny.toAddMonoidHom (α.dualIsogeny.toAddMonoidHom P) := by
    have := DFunLike.congr_fun htrace (α.dualIsogeny.toAddMonoidHom P)
    simp only [AddMonoidHom.add_apply, multiplicationByN_apply] at this
    exact this.symm
  have h_comp_apply : α.toAddMonoidHom (α.dualIsogeny.toAddMonoidHom P) =
      (α.degree : ℤ) • P :=
    α.comp_dualIsogeny_apply P
  rw [h_tr_apply, h_comp_apply]
  abel

/-- Theorem 6.18 (for `α̂`): the dual `α̂` also satisfies the characteristic equation
`λ² - (tr α) λ + deg α = 0`. -/
theorem Isogeny.char_poly_dualIsogeny
    (α : Isogeny E E) :
    α.dualIsogeny.toAddMonoidHom.comp α.dualIsogeny.toAddMonoidHom -
      (multiplicationByN E α.trace).comp
        α.dualIsogeny.toAddMonoidHom +
      multiplicationByN E (α.degree : ℤ) = 0 := by
  have htrace := α.toAddMonoidHom_add_dualIsogeny_eq_trace
  have hcomp_dual := α.comp_dualIsogeny
  ext P
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.add_apply,
             multiplicationByN_apply, AddMonoidHom.zero_apply]
  have h_tr_apply : α.trace •
      (α.dualIsogeny.toAddMonoidHom P) =
      α.toAddMonoidHom (α.dualIsogeny.toAddMonoidHom P) +
        α.dualIsogeny.toAddMonoidHom (α.dualIsogeny.toAddMonoidHom P) := by
    have := DFunLike.congr_fun htrace (α.dualIsogeny.toAddMonoidHom P)
    simp only [AddMonoidHom.add_apply, multiplicationByN_apply] at this
    exact this.symm
  have h_comp_apply : α.toAddMonoidHom (α.dualIsogeny.toAddMonoidHom P) =
      (α.degree : ℤ) • P :=
    α.comp_dualIsogeny_apply P
  rw [h_tr_apply, h_comp_apply]
  abel

end Theorem618

section Lemma619

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- Two endomorphisms `α, β` of `E` agree on `n`-torsion iff their underlying maps match
on `E[n]`. This is the predicate denoted `αₙ = βₙ` in Lemma 6.19. -/
def Isogeny.agreeOnTorsion (α β : Isogeny E E) (n : ℤ) : Prop :=
  ∀ (P : E.Point), P ∈ torsionSubgroup E n → α.toAddMonoidHom P = β.toAddMonoidHom P

/-- Cauchy-style interpolation for endomorphisms: if `α` and `β` agree on `E[n]` for a
sufficiently large `n` coprime to the characteristic and to both degrees, then globally
either `α = β` or `α = -β`. -/
theorem Isogeny.cauchy_interpolation_global_sign
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α β : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_size : n * n > 4 * max α.degree β.degree)
    (hn_cop_char : Nat.Coprime n (ringChar F))
    (hn_cop_α : Nat.Coprime n α.degree)
    (hn_cop_β : Nat.Coprime n β.degree)
    (hagree : ∀ (P : E.Point),
      P ∈ torsionSubgroup E (n : ℤ) → α.toAddMonoidHom P = β.toAddMonoidHom P) :
    α.toAddMonoidHom = β.toAddMonoidHom ∨
    α.toAddMonoidHom = -β.toAddMonoidHom := by sorry

/-- If `n` is coprime to `deg α`, then `α` restricted to `E[n]` is injective: the only
`n`-torsion point in the kernel of `α` is `0`. -/
theorem Isogeny.torsion_inter_kernel_trivial
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_cop : Nat.Coprime n α.degree) :
    ∀ (P : E.Point), P ∈ torsionSubgroup E (n : ℤ) →
      α.toAddMonoidHom P = 0 → P = 0 := by sorry

/-- Existence of an `n`-torsion point whose image under `α` is not `2`-torsion, used in
the sign resolution step of Lemma 6.19. -/
theorem Isogeny.exists_non_two_torsion_image
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_sq_gt : n * n > 4)
    (hn_cop_α : Nat.Coprime n α.degree) :
    ∃ (P : E.Point), P ∈ torsionSubgroup E (n : ℤ) ∧
      ¬ ((2 : ℤ) • (α.toAddMonoidHom P) = 0) := by sorry

/-- Pointwise version of the global `±` dichotomy: under the hypotheses of Lemma 6.19,
for every `P`, either `α(P) = β(P)` or `α(P) = -β(P)`. -/
theorem Isogeny.agree_on_torsion_implies_pm
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α β : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_size : n * n > 4 * max α.degree β.degree)
    (hn_cop_char : Nat.Coprime n (ringChar F))
    (hn_cop_α : Nat.Coprime n α.degree)
    (hn_cop_β : Nat.Coprime n β.degree)
    (hagree : ∀ (P : E.Point),
      P ∈ torsionSubgroup E (n : ℤ) → α.toAddMonoidHom P = β.toAddMonoidHom P) :
    ∀ (P : E.Point), α.toAddMonoidHom P = β.toAddMonoidHom P ∨
      α.toAddMonoidHom P = -β.toAddMonoidHom P := by
  have hglobal := Isogeny.cauchy_interpolation_global_sign α β n hn_pos hn_size
    hn_cop_char hn_cop_α hn_cop_β hagree
  intro P
  rcases hglobal with heq | hneg
  · left; exact DFunLike.congr_fun heq P
  · right
    have : (-β.toAddMonoidHom) P = -β.toAddMonoidHom P := rfl
    rw [← this]; exact DFunLike.congr_fun hneg P

/-- Sign-resolution step in Lemma 6.19: combining the pointwise `±` dichotomy with
agreement on `E[n]` and the non-`2`-torsion image, deduce `α = β`. -/
theorem Isogeny.sign_resolution
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α β : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_size : n * n > 4 * max α.degree β.degree)
    (hn_cop_char : Nat.Coprime n (ringChar F))
    (hn_cop_α : Nat.Coprime n α.degree)
    (hpm : ∀ (P : E.Point), α.toAddMonoidHom P = β.toAddMonoidHom P ∨
      α.toAddMonoidHom P = -β.toAddMonoidHom P)
    (hagree : ∀ (P : E.Point),
      P ∈ torsionSubgroup E (n : ℤ) → α.toAddMonoidHom P = β.toAddMonoidHom P) :
    α.toAddMonoidHom = β.toAddMonoidHom := by
  by_contra hne


  have hQ_ex : ∃ Q, α.toAddMonoidHom Q ≠ β.toAddMonoidHom Q := by
    by_contra h; push_neg at h; exact hne (AddMonoidHom.ext h)
  obtain ⟨Q, hQ_neq⟩ := hQ_ex
  have hQ_neg : α.toAddMonoidHom Q = -β.toAddMonoidHom Q := by
    rcases hpm Q with h | h
    · exact absurd h hQ_neq
    · exact h

  have h_sum_zero : ∀ P : E.Point, α.toAddMonoidHom P + β.toAddMonoidHom P = 0 := by
    intro P
    rcases hpm P with h | h
    ·


      have hQP_diff_ne : α.toAddMonoidHom (Q + P) - β.toAddMonoidHom (Q + P) ≠ 0 := by
        simp only [map_add]
        have : α.toAddMonoidHom Q + α.toAddMonoidHom P -
            (β.toAddMonoidHom Q + β.toAddMonoidHom P) =
            (α.toAddMonoidHom Q - β.toAddMonoidHom Q) +
            (α.toAddMonoidHom P - β.toAddMonoidHom P) := by abel
        rw [this, sub_eq_zero.mpr h, add_zero]
        exact sub_ne_zero.mpr hQ_neq
      rcases hpm (Q + P) with hQP | hQP
      · exact absurd (sub_eq_zero.mpr hQP) hQP_diff_ne
      ·
        have hQP_sum : α.toAddMonoidHom (Q + P) + β.toAddMonoidHom (Q + P) = 0 := by
          rw [hQP]; simp
        have hQ_sum : α.toAddMonoidHom Q + β.toAddMonoidHom Q = 0 := by
          rw [hQ_neg]; simp


        have : α.toAddMonoidHom P + β.toAddMonoidHom P =
            α.toAddMonoidHom (Q + P) + β.toAddMonoidHom (Q + P) -
            (α.toAddMonoidHom Q + β.toAddMonoidHom Q) := by
          simp only [map_add]; abel
        rw [this, hQP_sum, hQ_sum]; simp

    ·
      rw [h]; simp


  have hn_sq_gt : n * n > 4 := by
    have : 1 ≤ max α.degree β.degree :=
      le_max_of_le_left (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp α.degree_pos))
    omega
  obtain ⟨P₀, hP₀_tor, hP₀_not_2tor⟩ :=
    Isogeny.exists_non_two_torsion_image α n hn_pos hn_sq_gt hn_cop_α
  have h_agree_P₀ := hagree P₀ hP₀_tor
  have h_sum_P₀ := h_sum_zero P₀


  apply hP₀_not_2tor
  rw [two_smul]
  rw [h_agree_P₀] at h_sum_P₀ ⊢
  exact h_sum_P₀

/-- Auxiliary form of Lemma 6.19 stated with an unfolded agreement hypothesis: if `α` and
`β` agree on `E[n]` for `n` satisfying the size/coprimality conditions, then `α = β`. -/
theorem Isogeny.torsion_determines_endomorphism_aux
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α β : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_size : n * n > 4 * max α.degree β.degree)
    (hn_cop_char : Nat.Coprime n (ringChar F))
    (hn_cop_α : Nat.Coprime n α.degree)
    (hn_cop_β : Nat.Coprime n β.degree)
    (hagree : ∀ (P : E.Point),
      P ∈ torsionSubgroup E (n : ℤ) → α.toAddMonoidHom P = β.toAddMonoidHom P) :
    α.toAddMonoidHom = β.toAddMonoidHom := by

  have hpm := Isogeny.agree_on_torsion_implies_pm α β n hn_pos hn_size
    hn_cop_char hn_cop_α hn_cop_β hagree

  exact Isogeny.sign_resolution α β n hn_pos hn_size hn_cop_char hn_cop_α hpm hagree

/-- Lemma 6.19: for `n ≥ 2√m + 1` coprime to the characteristic and to `deg α`, `deg β`,
if `αₙ = βₙ` (i.e. `α` and `β` agree on `E[n]`) then `α = β`. -/
theorem Isogeny.torsion_determines_endomorphism
    (α β : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_size : n * n > 4 * max α.degree β.degree)
    (hn_cop_char : Nat.Coprime n (ringChar F))
    (hn_cop_α : Nat.Coprime n α.degree)
    (hn_cop_β : Nat.Coprime n β.degree)
    (hagree : Isogeny.agreeOnTorsion α β (n : ℤ)) :
    α.toAddMonoidHom = β.toAddMonoidHom := by
  unfold Isogeny.agreeOnTorsion at hagree
  exact Isogeny.torsion_determines_endomorphism_aux α β n hn_pos hn_size
    hn_cop_char hn_cop_α hn_cop_β hagree

/-- Pointwise form of Lemma 6.19: under the same hypotheses, `α(P) = β(P)` for every
point `P`. -/
theorem Isogeny.torsion_determines_endomorphism_apply
    (α β : Isogeny E E)
    (n : ℕ) (hn_pos : 0 < n)
    (hn_size : n * n > 4 * max α.degree β.degree)
    (hn_cop_char : Nat.Coprime n (ringChar F))
    (hn_cop_α : Nat.Coprime n α.degree)
    (hn_cop_β : Nat.Coprime n β.degree)
    (hagree : Isogeny.agreeOnTorsion α β (n : ℤ))
    (P : E.Point) :
    α.toAddMonoidHom P = β.toAddMonoidHom P := by
  have h := Isogeny.torsion_determines_endomorphism α β n hn_pos hn_size
    hn_cop_char hn_cop_α hn_cop_β hagree
  exact DFunLike.congr_fun h P

end Lemma619
