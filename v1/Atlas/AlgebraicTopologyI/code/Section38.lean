/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section17
import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section34
import Atlas.AlgebraicTopologyI.code.Section37
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear

noncomputable section

open Metric Set

namespace BorsukUlam

/-- The unit sphere in `EuclideanSpace ℝ (Fin (n+1))` is connected whenever `n ≥ 1`,
i.e. for spheres of dimension at least one. -/
lemma sphere_isConnected (n : ℕ) (hn : 1 ≤ n) :
    IsConnected (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  isConnected_sphere (by
    apply Module.lt_rank_of_lt_finrank
    rw [finrank_euclideanSpace_fin]
    omega) 0 (by norm_num)

/-- The `k`-th singular cohomology of real projective `n`-space `ℝPⁿ` with coefficients in
`𝔽₂ = ZMod 2`, packaged as a plain `Type`. Used to set up the Borsuk–Ulam proof via the
mod-2 cohomology ring of `ℝPⁿ`. -/
def F2CohomRPn (n k : ℕ) : Type :=
  (SingularCohomology.singularCohomology (ZMod 2)
    (TopCat.of (RealProjectiveSpace.RPn n))
    (ModuleCat.of (ZMod 2) (ZMod 2)) k : Type)

/-- The additive commutative group structure on `F2CohomRPn n k` inherited from its
`ModuleCat` representation. -/
@[reducible] def F2CohomRPn.instAddCommGroup (n k : ℕ) : AddCommGroup (F2CohomRPn n k) :=
  ModuleCat.isAddCommGroup
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)
attribute [instance] F2CohomRPn.instAddCommGroup

/-- The cup product `H^p(ℝPⁿ; 𝔽₂) ⊗ H^q(ℝPⁿ; 𝔽₂) → H^{p+q}(ℝPⁿ; 𝔽₂)` on mod-2 cohomology
of `ℝPⁿ`, exposed as a binary function on the underlying types. -/
noncomputable def F2CohomRPn.cupProduct (n p q : ℕ) :
    F2CohomRPn n p → F2CohomRPn n q → F2CohomRPn n (p + q) :=
  fun a b => (SingularCohomology.cupProduct (ZMod 2)
    (TopCat.of (RealProjectiveSpace.RPn n)) p q) (a ⊗ₜ[ZMod 2] b)

/-- The `ZMod 2`-module structure on `F2CohomRPn n k`, inherited from the underlying
`ModuleCat` object. -/
noncomputable instance F2CohomRPn.instModule (n k : ℕ) : Module (ZMod 2) (F2CohomRPn n k) :=
  ModuleCat.isModule
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)

/-- Every module over the field `ZMod 2` is free, so in particular
`H^k(ℝPⁿ; 𝔽₂)` is a free `𝔽₂`-module for `1 ≤ n` and `k ≤ n`. -/
theorem F2CohomRPn.instFree (n k : ℕ) (_hn : n ≥ 1) (_hk : k ≤ n) :
    Module.Free (ZMod 2) (F2CohomRPn n k) :=
  Module.Free.of_divisionRing (ZMod 2) (F2CohomRPn n k)

/-- For `1 ≤ n` and `k ≤ n`, the mod-2 cohomology group `H^k(ℝPⁿ; 𝔽₂)` is one-dimensional
over `𝔽₂`. This encodes the standard fact that `H^*(ℝPⁿ; 𝔽₂) ≅ 𝔽₂[x]/(x^{n+1})`. -/
theorem F2CohomRPn.finrank_eq_one (n k : ℕ) (hn : n ≥ 1) (hk : k ≤ n) :
    @Module.finrank (ZMod 2) (F2CohomRPn n k) _ (F2CohomRPn.instAddCommGroup n k).toAddCommMonoid
      (F2CohomRPn.instModule n k) = 1 := by sorry

/-- Since `H^k(ℝPⁿ; 𝔽₂)` is free of rank one over `𝔽₂` (for `1 ≤ n` and `k ≤ n`),
it is a finite `𝔽₂`-module. -/
theorem F2CohomRPn.instFinite (n k : ℕ) (hn : n ≥ 1) (hk : k ≤ n) :
    Module.Finite (ZMod 2) (F2CohomRPn n k) := by
  haveI := F2CohomRPn.instFree n k hn hk
  exact Module.finite_of_finrank_eq_succ (F2CohomRPn.finrank_eq_one n k hn hk)

/-- A canonical generator `x` of the one-dimensional `𝔽₂`-vector space
`H^1(ℝPⁿ; 𝔽₂)`. -/
noncomputable def F2CohomRPn.generator (n : ℕ) (hn : n ≥ 1) : F2CohomRPn n 1 :=
  haveI := F2CohomRPn.instFree n 1 hn hn
  haveI := F2CohomRPn.instFinite n 1 hn hn
  (LinearEquiv.ofFinrankEq (F2CohomRPn n 1) (ZMod 2)
    (by rw [F2CohomRPn.finrank_eq_one n 1 hn hn, Module.finrank_self])).symm
    (1 : ZMod 2)

/-- The canonical generator `1` of `H^0(ℝPⁿ; 𝔽₂) ≅ 𝔽₂`, i.e. the multiplicative unit of the
mod-2 cohomology ring. -/
noncomputable def F2CohomRPn.generatorPow_zero (n : ℕ) (hn : n ≥ 1) : F2CohomRPn n 0 :=
  haveI := F2CohomRPn.instFree n 0 hn (Nat.zero_le n)
  haveI := F2CohomRPn.instFinite n 0 hn (Nat.zero_le n)
  (LinearEquiv.ofFinrankEq (F2CohomRPn n 0) (ZMod 2)
    (by rw [F2CohomRPn.finrank_eq_one n 0 hn (Nat.zero_le n), Module.finrank_self])).symm
    (1 : ZMod 2)

/-- The `k`-th cup power `xᵏ ∈ H^k(ℝPⁿ; 𝔽₂)` of the canonical generator `x` in
`H^1(ℝPⁿ; 𝔽₂)`. -/
noncomputable def F2CohomRPn.generatorPow (n k : ℕ) (hn : n ≥ 1) : F2CohomRPn n k :=
  match k with
  | 0 => F2CohomRPn.generatorPow_zero n hn
  | k + 1 => F2CohomRPn.cupProduct n k 1
      (F2CohomRPn.generatorPow n k hn) (F2CohomRPn.generator n hn)

/-- The additive isomorphism `H^k(ℝPⁿ; 𝔽₂) ≃+ 𝔽₂` for `1 ≤ n` and `k ≤ n`, obtained
from the fact that this cohomology group is one-dimensional over `𝔽₂`. -/
noncomputable def F2CohomRPn.cohomIsoF2 (n k : ℕ) (hn : n ≥ 1) (hk : k ≤ n) :
    F2CohomRPn n k ≃+ ZMod 2 :=
  haveI := F2CohomRPn.instFree n k hn hk
  haveI := F2CohomRPn.instFinite n k hn hk
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  (LinearEquiv.ofFinrankEq (F2CohomRPn n k) (ZMod 2)
    (by rw [F2CohomRPn.finrank_eq_one n k hn hk, Module.finrank_self])).toAddEquiv

/-- Under the additive isomorphism `H^k(ℝPⁿ; 𝔽₂) ≃+ 𝔽₂`, the cup power `xᵏ` is sent to
the unit `1 ∈ 𝔽₂`. In particular `xᵏ ≠ 0` for `k ≤ n`. -/
theorem F2CohomRPn.cohomIsoF2_generatorPow (n k : ℕ) (hn : n ≥ 1) (hk : k ≤ n) :
    F2CohomRPn.cohomIsoF2 n k hn hk (F2CohomRPn.generatorPow n k hn) = 1 := by sorry

/-- The first cup power `x¹` agrees with the canonical generator `x` of
`H^1(ℝPⁿ; 𝔽₂)`. -/
theorem F2CohomRPn.generatorPow_one (n : ℕ) (hn : n ≥ 1) :
    F2CohomRPn.generatorPow n 1 hn = F2CohomRPn.generator n hn := by
  have h1 := F2CohomRPn.cohomIsoF2_generatorPow n 1 hn hn
  have h2 : F2CohomRPn.cohomIsoF2 n 1 hn hn (F2CohomRPn.generator n hn) = 1 := by
    simp only [F2CohomRPn.generator, F2CohomRPn.cohomIsoF2]
    simp [LinearEquiv.coe_toAddEquiv, LinearEquiv.apply_symm_apply]
  exact (F2CohomRPn.cohomIsoF2 n 1 hn hn).injective (h1.trans h2.symm)

/-- The top cup power `xⁿ ∈ H^n(ℝPⁿ; 𝔽₂)` is nonzero. This is the key nonvanishing
fact used in the proof of Borsuk–Ulam. -/
theorem F2CohomRPn.generatorPow_ne_zero (n : ℕ) (hn : n ≥ 1) :
    F2CohomRPn.generatorPow n n hn ≠ 0 := by
  intro h
  have h1 := F2CohomRPn.cohomIsoF2_generatorPow n n hn le_rfl
  rw [h, map_zero] at h1
  haveI : Fact (1 < 2) := ⟨by norm_num⟩
  exact zero_ne_one h1

/-- If the integral singular homology `H_k(X; ℤ)` vanishes, then the mod-2 singular
cochain complex of `X` is exact at degree `k`. A universal-coefficient style transfer
of vanishing from homology to cohomology. -/
theorem singularHomology_isZero_implies_F2_cochain_exact
    (X : TopCat.{0}) (k : ℕ)
    (h_homol : CategoryTheory.Limits.IsZero
      ((((AlgebraicTopology.singularChainComplexFunctor.{0} AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).obj X).homology k)) :
    (SingularCohomology.singularCochainComplex (ZMod 2) X
      (ModuleCat.of (ZMod 2) (ZMod 2))).ExactAt k := by sorry

/-- For `k > n`, the mod-2 singular cochain complex of `ℝPⁿ` is exact at degree `k`.
This is the cohomological vanishing above the dimension of the CW complex `ℝPⁿ`. -/
theorem rpn_singularCochainComplex_exactAt (n k : ℕ) (hk : k > n) :
    (SingularCohomology.singularCochainComplex (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2))).ExactAt k := by


  haveI : T2Space (RealProjectiveSpace.RPn n) := RealProjectiveSpace.rpn_t2Space n
  haveI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace.RPn n)) :=
    RealProjectiveSpace.rpn_cwComplex n
  have h_cell := RealProjectiveSpace.rpn_homology_gt n k hk

  have h_sing : CategoryTheory.Limits.IsZero
      (AlgebraicTopologyI.SingularHomologyGroup k (RealProjectiveSpace.RPn n)) := by
    exact h_cell.of_iso
      (@CWHomology.cellularHomologyGroup_iso_singularHomologyGroup k
        (RealProjectiveSpace.RPn n) _ (RealProjectiveSpace.rpn_t2Space n)
        (RealProjectiveSpace.rpn_cwComplex n)).symm


  rw [AlgebraicTopologyI.singularHomologyGroup_eq_homology] at h_sing
  exact singularHomology_isZero_implies_F2_cochain_exact
    (TopCat.of (RealProjectiveSpace.RPn n)) k h_sing


/-- Vanishing of `H^k(ℝPⁿ; 𝔽₂)` above the dimension: for `k > n`, the group has at most
one element. -/
theorem F2CohomRPn.vanishing (n k : ℕ) (hk : k > n) :
    Subsingleton (F2CohomRPn n k) := by

  have h_exact := rpn_singularCochainComplex_exactAt n k hk

  have h_isZero : CategoryTheory.Limits.IsZero
      (SingularCohomology.singularCohomology (ZMod 2)
        (TopCat.of (RealProjectiveSpace.RPn n))
        (ModuleCat.of (ZMod 2) (ZMod 2)) k) :=
    h_exact.isZero_homology

  exact ModuleCat.isZero_iff_subsingleton.mp h_isZero

/-- Functoriality of mod-2 cohomology: a continuous map `f : ℝPⁿ¹ → ℝPⁿ²` induces an
additive pullback `f* : H^k(ℝPⁿ²; 𝔽₂) → H^k(ℝPⁿ¹; 𝔽₂)`. -/
noncomputable def F2CohomRPn.cohomologyPullback
    {n₁ n₂ : ℕ}
    (f : C(RealProjectiveSpace.RPn n₁, RealProjectiveSpace.RPn n₂))
    (k : ℕ) : F2CohomRPn n₂ k →+ F2CohomRPn n₁ k :=
  (SingularCohomology.singularCohomologyMap (ZMod 2)
    (TopCat.ofHom f) k).hom.toAddMonoidHom

/-- An antipodal-preserving continuous map `g : Sᵐ → Sᵐ⁻¹` descends to the quotient by the
antipodal action to yield a continuous map `ℝPᵐ → ℝPᵐ⁻¹`. Defined for `m ≥ 2`. -/
noncomputable def F2CohomRPn.descendedMap : (m : ℕ) → (hm : m ≥ 2) →
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1))) →
    (hg : ∀ x, g (-x) = -g x) →
    C(RealProjectiveSpace.RPn m, RealProjectiveSpace.RPn (m - 1))
  | n + 2, _, g, hg =>
    ⟨Quotient.lift
      (fun x : RealProjectiveSpace.Sphere (n + 2) =>
        @Quotient.mk' (RealProjectiveSpace.Sphere (n + 1))
          (RealProjectiveSpace.antipodalSetoid (n + 1)) (g x))
      (fun a b hab => by
        rcases hab with hab | hab
        · congr 1; exact Subtype.ext hab
        · apply Quotient.sound
          show (↑(g a) : EuclideanSpace ℝ (Fin (n + 2))) = ↑(g b) ∨
               (↑(g a) : EuclideanSpace ℝ (Fin (n + 2))) = -↑(g b)
          right
          have heq : a = -b := Subtype.ext hab
          have := hg b; rw [← heq] at this
          exact congrArg Subtype.val this),
      (continuous_quotient_mk' (s := RealProjectiveSpace.antipodalSetoid (n + 1))).comp
        g.continuous |>.quotient_lift _⟩
  | 0, hm, _, _ => absurd hm (by omega)
  | 1, hm, _, _ => absurd hm (by omega)

/-- The cohomology pullback `H^k(ℝPᵐ⁻¹; 𝔽₂) → H^k(ℝPᵐ; 𝔽₂)` induced by an odd map
`g : Sᵐ → Sᵐ⁻¹` via its descent `ℝPᵐ → ℝPᵐ⁻¹`. -/
noncomputable def F2CohomRPn.pullback (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (k : ℕ) : F2CohomRPn (m - 1) k →+ F2CohomRPn m k :=
  F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) k

/-- The descended map of an odd `g : Sᵐ → Sᵐ⁻¹` pulls the canonical degree-1 mod-2
cohomology generator of `ℝPᵐ⁻¹` back to the canonical degree-1 generator of `ℝPᵐ`. -/
theorem F2CohomRPn.descendedMap_pullback_generator (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (hm1 : m - 1 ≥ 1) :
    F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) 1
      (F2CohomRPn.generator (m - 1) hm1) = F2CohomRPn.generator m (by omega) := by sorry

/-- The pullback map on `H^1` induced by the descent of an odd `g : Sᵐ → Sᵐ⁻¹` is
nonzero: it sends the canonical generator to a nonzero class. -/
theorem F2CohomRPn.descendedMap_pullback_ne_zero (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x) :
    F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) 1 ≠ 0 := by
  intro h

  have hgen_zero : F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) 1
      (F2CohomRPn.generator (m - 1) (by omega : m - 1 ≥ 1)) = 0 :=
    DFunLike.congr_fun h _

  have hgen_eq := F2CohomRPn.descendedMap_pullback_generator m hm g hg (by omega : m - 1 ≥ 1)

  have hgen_ne : F2CohomRPn.generator m (by omega : m ≥ 1) ≠ 0 := by
    intro heq
    have h1 : F2CohomRPn.cohomIsoF2 m 1 (by omega) (by omega)
        (F2CohomRPn.generator m (by omega)) = 1 := by
      rw [← F2CohomRPn.generatorPow_one m (by omega)]
      exact F2CohomRPn.cohomIsoF2_generatorPow m 1 (by omega) (by omega)
    rw [heq, map_zero] at h1
    exact zero_ne_one h1

  exact hgen_ne (hgen_eq ▸ hgen_zero)

/-- Auxiliary version of `pullback_generator_ne_zero` proved directly from the
`descendedMap_pullback_ne_zero` lemma, before being repackaged. -/
theorem F2CohomRPn.pullback_generator_ne_zero_ax (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (hm1 : m - 1 ≥ 1) :
    F2CohomRPn.pullback m hm g hg 1 (F2CohomRPn.generator (m - 1) hm1) ≠ 0 := by

  have hne : F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) 1 ≠ 0 :=
    F2CohomRPn.descendedMap_pullback_ne_zero m hm g hg


  intro h
  apply hne


  haveI := F2CohomRPn.instFree (m - 1) 1 hm1 (by omega : 1 ≤ m - 1)
  haveI := F2CohomRPn.instFinite (m - 1) 1 hm1 (by omega : 1 ≤ m - 1)

  set φ := F2CohomRPn.cohomIsoF2 (m - 1) 1 hm1 (by omega : 1 ≤ m - 1)

  have hgen_eq : φ (F2CohomRPn.generator (m - 1) hm1) = 1 := by
    rw [← F2CohomRPn.generatorPow_one (m - 1) hm1]
    exact F2CohomRPn.cohomIsoF2_generatorPow (m - 1) 1 hm1 (by omega)


  have h' : (F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) 1)
      (F2CohomRPn.generator (m - 1) hm1) = 0 := h


  ext x
  show (F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) 1) x = 0

  have hx_class : x = 0 ∨ x = F2CohomRPn.generator (m - 1) hm1 := by
    by_cases hx0 : φ x = 0
    · left; exact φ.injective (by rw [hx0, map_zero])
    · right
      have : φ x = 1 := by
        have : (φ x : ZMod 2) ≠ 0 := hx0
        exact Fin.eq_one_of_ne_zero _ this
      exact φ.injective (by rw [this, hgen_eq])
  rcases hx_class with rfl | rfl
  · simp [map_zero]
  · exact h'

/-- The pullback along the descent of an odd `g : Sᵐ → Sᵐ⁻¹` sends the canonical generator
of `H^1(ℝPᵐ⁻¹; 𝔽₂)` to a nonzero element of `H^1(ℝPᵐ; 𝔽₂)`. -/
theorem F2CohomRPn.pullback_generator_ne_zero (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (hm1 : m - 1 ≥ 1) :
    F2CohomRPn.pullback m hm g hg 1 (F2CohomRPn.generator (m - 1) hm1) ≠ 0 :=
  F2CohomRPn.pullback_generator_ne_zero_ax m hm g hg hm1

/-- The pullback along the descent of an odd `g : Sᵐ → Sᵐ⁻¹` sends the canonical generator
of `H^1(ℝPᵐ⁻¹; 𝔽₂)` exactly to the canonical generator of `H^1(ℝPᵐ; 𝔽₂)`. -/
theorem F2CohomRPn.pullback_generator (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (hm1 : m - 1 ≥ 1) :
    F2CohomRPn.pullback m hm g hg 1 (F2CohomRPn.generator (m - 1) hm1) =
      F2CohomRPn.generator m (by omega) := by

  set φ := F2CohomRPn.cohomIsoF2 m 1 (by omega : m ≥ 1) (by omega : 1 ≤ m)

  have hgen_eq : φ (F2CohomRPn.generator m (by omega)) = 1 := by
    rw [← F2CohomRPn.generatorPow_one m (by omega)]
    exact F2CohomRPn.cohomIsoF2_generatorPow m 1 (by omega) (by omega)

  have hne : F2CohomRPn.pullback m hm g hg 1 (F2CohomRPn.generator (m - 1) hm1) ≠ 0 :=
    F2CohomRPn.pullback_generator_ne_zero m hm g hg hm1

  have hpb_ne : φ (F2CohomRPn.pullback m hm g hg 1 (F2CohomRPn.generator (m - 1) hm1)) ≠ 0 := by
    intro h
    exact hne (φ.injective (by rwa [map_zero]))
  have hpb_eq : φ (F2CohomRPn.pullback m hm g hg 1 (F2CohomRPn.generator (m - 1) hm1)) = 1 :=
    Fin.eq_one_of_ne_zero _ hpb_ne

  exact φ.injective (hpb_eq.trans hgen_eq.symm)

/-- Any continuous map `ℝPⁿ² → ℝPⁿ¹` induces an isomorphism on mod-2 cohomology in
degree 0. Both groups are isomorphic to `𝔽₂` and the map preserves the unit. -/
theorem F2CohomRPn.singularCohomologyMap_degree0_isIso
    (n₁ n₂ : ℕ) (hn₁ : n₁ ≥ 1) (hn₂ : n₂ ≥ 1)
    (f : C(RealProjectiveSpace.RPn n₂, RealProjectiveSpace.RPn n₁)) :
    CategoryTheory.IsIso (SingularCohomology.singularCohomologyMap (ZMod 2)
      (TopCat.ofHom f) 0) := by sorry

/-- The cohomology pullback of the multiplicative unit `1 ∈ H^0(ℝPⁿ¹; 𝔽₂)` along any
continuous map `f : ℝPⁿ² → ℝPⁿ¹` is nonzero. -/
theorem F2CohomRPn.cohomologyPullback_unit_ne_zero
    (n₁ n₂ : ℕ) (hn₁ : n₁ ≥ 1) (hn₂ : n₂ ≥ 1)
    (f : C(RealProjectiveSpace.RPn n₂, RealProjectiveSpace.RPn n₁)) :
    F2CohomRPn.cohomologyPullback f 0 (F2CohomRPn.generatorPow n₁ 0 hn₁) ≠ 0 := by

  haveI h_iso := F2CohomRPn.singularCohomologyMap_degree0_isIso n₁ n₂ hn₁ hn₂ f

  have hgen_ne : F2CohomRPn.generatorPow n₁ 0 hn₁ ≠ 0 := by
    intro h
    have h1 := F2CohomRPn.cohomIsoF2_generatorPow n₁ 0 hn₁ (Nat.zero_le n₁)
    rw [h, map_zero] at h1
    exact zero_ne_one h1


  intro h_eq_zero

  have h_inj : Function.Injective
      (SingularCohomology.singularCohomologyMap (ZMod 2)
        (TopCat.ofHom f) 0).hom :=
    (CategoryTheory.asIso (SingularCohomology.singularCohomologyMap (ZMod 2)
        (TopCat.ofHom f) 0)).toLinearEquiv.injective


  have h_gen_zero : F2CohomRPn.generatorPow n₁ 0 hn₁ = 0 :=
    h_inj (show (SingularCohomology.singularCohomologyMap (ZMod 2)
        (TopCat.ofHom f) 0).hom (F2CohomRPn.generatorPow n₁ 0 hn₁) =
        (SingularCohomology.singularCohomologyMap (ZMod 2)
        (TopCat.ofHom f) 0).hom 0 by rw [map_zero]; exact h_eq_zero)
  exact hgen_ne h_gen_zero

/-- The cohomology pullback along `f : ℝPⁿ² → ℝPⁿ¹` sends the multiplicative unit of
`H^0(ℝPⁿ¹; 𝔽₂)` to the multiplicative unit of `H^0(ℝPⁿ²; 𝔽₂)`. -/
theorem F2CohomRPn.cohomologyPullback_preserves_unit
    (n₁ n₂ : ℕ) (hn₁ : n₁ ≥ 1) (hn₂ : n₂ ≥ 1)
    (f : C(RealProjectiveSpace.RPn n₂, RealProjectiveSpace.RPn n₁)) :
    F2CohomRPn.cohomologyPullback f 0 (F2CohomRPn.generatorPow n₁ 0 hn₁) =
      F2CohomRPn.generatorPow n₂ 0 hn₂ := by

  set φ := F2CohomRPn.cohomIsoF2 n₂ 0 hn₂ (Nat.zero_le n₂)

  have hgen_eq : φ (F2CohomRPn.generatorPow n₂ 0 hn₂) = 1 :=
    F2CohomRPn.cohomIsoF2_generatorPow n₂ 0 hn₂ (Nat.zero_le n₂)

  have hne : F2CohomRPn.cohomologyPullback f 0 (F2CohomRPn.generatorPow n₁ 0 hn₁) ≠ 0 :=
    F2CohomRPn.cohomologyPullback_unit_ne_zero n₁ n₂ hn₁ hn₂ f

  have hpb_ne : φ (F2CohomRPn.cohomologyPullback f 0 (F2CohomRPn.generatorPow n₁ 0 hn₁)) ≠ 0 := by
    intro h
    exact hne (φ.injective (by rwa [map_zero]))
  have hpb_eq : φ (F2CohomRPn.cohomologyPullback f 0 (F2CohomRPn.generatorPow n₁ 0 hn₁)) = 1 :=
    Fin.eq_one_of_ne_zero _ hpb_ne

  exact φ.injective (hpb_eq.trans hgen_eq.symm)

/-- Unfolding identity: the `(k+1)`-th cup power equals the cup product of the `k`-th
cup power with the generator `x`. -/
theorem F2CohomRPn.generatorPow_succ (n k : ℕ) (hn : n ≥ 1) :
    F2CohomRPn.generatorPow n (k + 1) hn =
      F2CohomRPn.cupProduct n k 1 (F2CohomRPn.generatorPow n k hn)
        (F2CohomRPn.generator n hn) := by
  simp [F2CohomRPn.generatorPow]


/-- Naturality of the cup product: for `f : X ⟶ Y`, the diagram
`(cup on Y) ∘ f* = f* ⊗ f* ∘ (cup on X)` commutes. -/
theorem SingularCohomology.cupProduct_naturality_hom
    (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (SingularCohomology.cupProduct R Y p q)
      (SingularCohomology.singularCohomologyMap R f (p + q)) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategory.tensorHom
        (SingularCohomology.singularCohomologyMap R f p)
        (SingularCohomology.singularCohomologyMap R f q))
      (SingularCohomology.cupProduct R X p q) := by sorry

/-- Naturality of the cup product on mod-2 cohomology of real projective spaces:
`f*(α ∪ β) = f* α ∪ f* β`. -/
theorem F2CohomRPn.cohomologyPullback_preserves_cupProduct
    (n₁ n₂ : ℕ)
    (f : C(RealProjectiveSpace.RPn n₂, RealProjectiveSpace.RPn n₁))
    (p q : ℕ)
    (α : F2CohomRPn n₁ p) (β : F2CohomRPn n₁ q) :
    F2CohomRPn.cohomologyPullback f (p + q)
      (F2CohomRPn.cupProduct n₁ p q α β) =
    F2CohomRPn.cupProduct n₂ p q
      (F2CohomRPn.cohomologyPullback f p α)
      (F2CohomRPn.cohomologyPullback f q β) := by

  show (SingularCohomology.singularCohomologyMap (ZMod 2) (TopCat.ofHom f) (p + q)).hom
    ((SingularCohomology.cupProduct (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n₁)) p q).hom (α ⊗ₜ[ZMod 2] β)) =
    (SingularCohomology.cupProduct (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n₂)) p q).hom
      ((SingularCohomology.singularCohomologyMap (ZMod 2) (TopCat.ofHom f) p).hom α ⊗ₜ[ZMod 2]
       (SingularCohomology.singularCohomologyMap (ZMod 2) (TopCat.ofHom f) q).hom β)

  have key := SingularCohomology.cupProduct_naturality_hom (ZMod 2) (TopCat.ofHom f) p q

  have h' := congrFun (congrArg (fun g => g.hom) key) (α ⊗ₜ[ZMod 2] β)
  simp only [CategoryTheory.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  convert h' using 1

/-- If a map `f : ℝPⁿ² → ℝPⁿ¹` sends the degree-1 generator to the degree-1 generator,
then by naturality of cup products it sends every cup power `xᵏ` to `xᵏ`. -/
theorem F2CohomRPn.cohomologyPullback_preserves_generatorPow
    (n₁ n₂ : ℕ) (hn₁ : n₁ ≥ 1) (hn₂ : n₂ ≥ 1)
    (f : C(RealProjectiveSpace.RPn n₂, RealProjectiveSpace.RPn n₁))
    (hf : F2CohomRPn.cohomologyPullback f 1 (F2CohomRPn.generator n₁ hn₁) =
          F2CohomRPn.generator n₂ hn₂)
    (k : ℕ) :
    F2CohomRPn.cohomologyPullback f k (F2CohomRPn.generatorPow n₁ k hn₁) =
      F2CohomRPn.generatorPow n₂ k hn₂ := by
  induction k with
  | zero =>

    exact F2CohomRPn.cohomologyPullback_preserves_unit n₁ n₂ hn₁ hn₂ f
  | succ k ih =>

    rw [F2CohomRPn.generatorPow_succ n₁ k hn₁]
    rw [F2CohomRPn.cohomologyPullback_preserves_cupProduct n₁ n₂ f k 1]
    rw [ih, hf]
    rw [← F2CohomRPn.generatorPow_succ n₂ k hn₂]

/-- For every `k`, the pullback induced by an odd `g : Sᵐ → Sᵐ⁻¹` sends the `k`-th cup
power `xᵏ ∈ H^k(ℝPᵐ⁻¹; 𝔽₂)` to `xᵏ ∈ H^k(ℝPᵐ; 𝔽₂)`. -/
theorem F2CohomRPn.pullback_generatorPow (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (k : ℕ) (hm1 : m - 1 ≥ 1) :
    F2CohomRPn.pullback m hm g hg k (F2CohomRPn.generatorPow (m - 1) k hm1) =
      F2CohomRPn.generatorPow m k (by omega) := by


  have hgen : F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) 1
      (F2CohomRPn.generator (m - 1) hm1) = F2CohomRPn.generator m (by omega) :=
    F2CohomRPn.pullback_generator m hm g hg hm1

  exact F2CohomRPn.cohomologyPullback_preserves_generatorPow
    (m - 1) m hm1 (by omega)
    (F2CohomRPn.descendedMap m hm g hg)
    hgen k

/-- There is no continuous odd map `Sⁿ⁺² → Sⁿ⁺¹`. The proof uses the nonvanishing of
the top cup power `xⁿ⁺² ∈ H^{n+2}(ℝPⁿ⁺²; 𝔽₂)` together with the vanishing of
`H^{n+2}(ℝPⁿ⁺¹; 𝔽₂)`. This is the key step in Borsuk–Ulam for dimensions `≥ 2`. -/
theorem no_odd_map_sphere (n : ℕ)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))
    (hg : ∀ x, g (-x) = -g x) : False := by


  have hpull := F2CohomRPn.pullback_generatorPow (n + 2) (by omega) g hg
      (n + 2) (by omega)


  have hne := F2CohomRPn.generatorPow_ne_zero (n + 2) (by omega)


  have hzero : F2CohomRPn.generatorPow (n + 2 - 1) (n + 2) (by omega) = 0 :=
    @Subsingleton.elim _ (F2CohomRPn.vanishing (n + 2 - 1) (n + 2) (by omega)) _ _


  apply hne
  rw [← hpull, hzero, map_zero]

/-- Borsuk–Ulam in dimensions `≥ 2`: every continuous map `Sⁿ⁺² → ℝⁿ⁺²` identifies some
pair of antipodal points, i.e. there exists `x` with `f x = f (-x)`. Deduced from
`no_odd_map_sphere` by normalising `f x - f (-x)` to a hypothetical odd map to the
sphere. -/
theorem borsuk_ulam_ge2 (n : ℕ)
    (f : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1),
          EuclideanSpace ℝ (Fin (n + 2)))) :
    ∃ x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1), f x = f (-x) := by

  by_contra h
  push Not at h

  have hne : ∀ x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1),
      f x - f (-x) ≠ 0 := fun x => sub_ne_zero.mpr (h x)
  have hnorm_pos : ∀ x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1),
      (0 : ℝ) < ‖f x - f (-x)‖ := fun x => norm_pos_iff.mpr (hne x)

  have hd_cont : Continuous (fun x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1) =>
      f x - f (-x)) :=
    f.continuous.sub (f.continuous.comp continuous_neg)

  have hφ_cont : Continuous (fun x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1) =>
      (‖f x - f (-x)‖⁻¹) • (f x - f (-x))) :=
    ((continuous_norm.comp hd_cont).inv₀ (fun x => ne_of_gt (hnorm_pos x))).smul hd_cont

  have hφ_norm : ∀ x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1),
      ‖(‖f x - f (-x)‖⁻¹) • (f x - f (-x))‖ = 1 := by
    intro x
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt (hnorm_pos x))

  have hφ_mem : ∀ x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1),
      (‖f x - f (-x)‖⁻¹) • (f x - f (-x)) ∈
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
    intro x; rw [mem_sphere_zero_iff_norm]; exact hφ_norm x

  let g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1),
            ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :=
    ⟨fun x => ⟨(‖f x - f (-x)‖⁻¹) • (f x - f (-x)), hφ_mem x⟩,
     hφ_cont.subtype_mk _⟩

  have hg_odd : ∀ x, g (-x) = -g x := by
    intro x
    refine Subtype.ext ?_


    show (‖f (-x) - f (-(-x))‖⁻¹) • (f (-x) - f (-(-x))) =
      -((‖f x - f (-x)‖⁻¹) • (f x - f (-x)))
    rw [neg_neg]
    rw [show f (-x) - f x = -(f x - f (-x)) from (neg_sub (f x) (f (-x))).symm]
    rw [norm_neg, smul_neg]

  exact no_odd_map_sphere n g hg_odd

/-- The Borsuk–Ulam theorem (Theorem 38.11). Thinking of `Sⁿ` as the unit vectors in
`ℝⁿ⁺¹`, every continuous function `f : Sⁿ → ℝⁿ` admits a point `x ∈ Sⁿ` with
`f x = f (-x)`. Proved by cases: `n = 0` (sphere is two-point), `n = 1` (intermediate
value theorem on the circle), `n ≥ 2` (`borsuk_ulam_ge2`). -/
theorem borsuk_ulam (n : ℕ)
    (f : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
          EuclideanSpace ℝ (Fin n))) :
    ∃ x : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1), f x = f (-x) := by
  match n with
  | 0 =>

    obtain ⟨x⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin 1)) (by norm_num : (0 : ℝ) ≤ 1)
    exact ⟨x, Subsingleton.elim _ _⟩
  | 1 =>


    have hconn := sphere_isConnected 1 le_rfl
    obtain ⟨a, ha⟩ := hconn.nonempty
    have hna : -a ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [mem_sphere_zero_iff_norm] at ha ⊢; simp [ha]
    let φ : ↥(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → ℝ := fun x => (f x) 0
    let ψ : ↥(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → ℝ := fun x => (f (-x)) 0
    have neg_neg_eq : (-⟨-a, hna⟩ : ↥(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) = ⟨a, ha⟩ :=
      Subtype.ext (by simp)
    have key2 : ψ ⟨-a, hna⟩ = φ ⟨a, ha⟩ := by simp only [ψ, φ]; rw [neg_neg_eq]
    have key1 : φ ⟨-a, hna⟩ = ψ ⟨a, ha⟩ := rfl
    haveI : ConnectedSpace ↥(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      isConnected_iff_connectedSpace.mp hconn
    have hφc : Continuous φ := (PiLp.continuous_apply 2 _ 0).comp f.continuous
    have hψc : Continuous ψ :=
      (PiLp.continuous_apply 2 _ 0).comp (f.continuous.comp continuous_neg)
    rcases le_total (φ ⟨a, ha⟩) (ψ ⟨a, ha⟩) with h | h
    · obtain ⟨x, _, heq⟩ := isPreconnected_univ.intermediate_value₂
        (mem_univ ⟨a, ha⟩) (mem_univ ⟨-a, hna⟩) hφc.continuousOn hψc.continuousOn
        h (by rw [key2, key1]; exact h)
      exact ⟨x, PiLp.ext (fun ⟨i, hi⟩ => by interval_cases i; exact heq)⟩
    · obtain ⟨x, _, heq⟩ := isPreconnected_univ.intermediate_value₂
        (mem_univ ⟨a, ha⟩) (mem_univ ⟨-a, hna⟩) hψc.continuousOn hφc.continuousOn
        h (by rw [key2, key1]; exact h)
      exact ⟨x, PiLp.ext (fun ⟨i, hi⟩ => by interval_cases i; exact heq.symm)⟩
  | n + 2 =>

    exact borsuk_ulam_ge2 n f

end BorsukUlam

open Manifold CategoryTheory

namespace PoincareDuality

variable (R : Type) [CommRing R]

/-- Poincaré–Lefschetz duality (Theorem 38.1) for an `R`-oriented `d`-manifold along a
compact set `K`: capping with the fundamental class `[M]_K` gives an isomorphism
`Ȟ^p(K; R) ≅ H_q(M, M\K; R)` whenever `p + q = d`. -/
noncomputable def capProduct_cechCohomology_iso
    (d : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    (K : Set M) (hK : IsCompact K)
    [hOr : IsROrientedAlong R d M K]
    (p q : ℕ) (hpq : p + q = d) :
    cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q :=
  poincareDualityCompact R d M K hK p q hpq

/-- Corollary 38.2: for `K` a compact subset of an `R`-oriented `d`-manifold and `p > d`,
the Čech cohomology `Ȟ^p(K; R)` vanishes. -/
theorem cech_cohomology_vanishing
    (d : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    (K : Set M) (hK : IsCompact K)
    [IsROrientedAlong R d M K]
    (p : ℕ) (hp : p > d) :
    Subsingleton (cechCohomology R M K ∅ p : Type) := by sorry


/-- Variant of Corollary 38.2 expressed for any `C⁰` `d`-manifold (with no orientation
hypothesis): for a compact set `K` and `p > d`, `Ȟ^p(K; R)` is a subsingleton. -/
theorem cechCohomology_subsingleton_of_gt_dim
    (d : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    [IsManifold (𝓡 d) 0 M]
    (K : Set M) (hK : IsCompact K)
    (p : ℕ) (hp : p > d) :
    Subsingleton (cechCohomology R M K ∅ p : Type) := by sorry


/-- Reduced singular homology `\widetilde H_q(X; R)`: in degree zero it is the kernel of
the augmentation `H_0(X; R) → R`, and in higher degrees it agrees with the usual
singular homology. -/
def ReducedSingularHomology
    (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (q : ℕ) : Type :=
  match q with
  | 0 => ↥(LinearMap.ker (augmentationH0 R (TopCat.of X)).hom)
  | n + 1 => (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1) : Type)


/-- The additive commutative group structure on reduced singular homology, inherited
from the augmentation kernel (degree 0) or from singular homology (higher degrees). -/
instance ReducedSingularHomology.instAddCommGroup
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    AddCommGroup (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.addCommGroup _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isAddCommGroup

/-- The `R`-module structure on reduced singular homology. -/
instance ReducedSingularHomology.instModule
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    Module R (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.module _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isModule

/-- Convenient abbreviation for the unit sphere `Sⁿ ⊂ ℝⁿ⁺¹` viewed as a subtype. -/
abbrev SphereType (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- Alexander duality on the sphere: for `K` compact in `Sⁿ` and `1 ≤ q ≤ n - 1`,
the Čech cohomology `Ȟ^q(K; R)` is isomorphic to the reduced singular homology
`\widetilde H_{n-q-1}(Sⁿ \ K; R)`. -/
theorem cech_cohomology_sphere_complement_iso
    {n : ℕ} (K : Set (SphereType n))
    (hK : IsCompact K)
    (q : ℕ) (hq : q ≥ 1) (hqn : q ≤ n - 1) :
    Nonempty (
      (cechCohomology R (SphereType n) K ∅ q : Type) ≃ₗ[R]
      ReducedSingularHomology R ↥(Kᶜ) (n - q - 1)) := by sorry


/-- Euclidean space `ℝⁿ` is `R`-orientable along the whole space `univ`; equivalently, it
carries a global `R`-orientation. -/
theorem euclideanSpace_isROrientedAlong_univ
    {n : ℕ} :
    IsROrientedAlong R n (EuclideanSpace ℝ (Fin n)) Set.univ := by sorry

/-- Euclidean space `ℝⁿ` is `R`-orientable along any subset `K`, obtained by restricting
the global orientation from `univ`. -/
theorem euclideanSpace_isROrientedAlong
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsROrientedAlong R n (EuclideanSpace ℝ (Fin n)) K :=
  isROrientedAlong_of_subset R n (EuclideanSpace ℝ (Fin n)) Set.univ K
    (Set.subset_univ K) (euclideanSpace_isROrientedAlong_univ R)

/-- Reduced singular homology of contractible Euclidean space vanishes in every degree:
`\widetilde H_q(ℝⁿ; R) = 0`. -/
theorem euclideanSpace_reduced_homology_vanishes
    {n : ℕ} (q : ℕ) :
    Subsingleton (ReducedSingularHomology R (EuclideanSpace ℝ (Fin n)) q) := by sorry

/-- Boundary isomorphism from the long exact sequence of the pair `(ℝⁿ, ℝⁿ \ K)` when
the ambient space is acyclic: `H_q(ℝⁿ, ℝⁿ \ K; R) ≃ \widetilde H_{q-1}(ℝⁿ \ K; R)`. -/
noncomputable def les_boundary_iso_of_acyclic_ambient
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (q : ℕ)
    (hAcyclic : ∀ q, Subsingleton (ReducedSingularHomology R (EuclideanSpace ℝ (Fin n)) q)) :
    (relativeSingularHomology R (↥((∅ : Set (EuclideanSpace ℝ (Fin n)))ᶜ))
      (Subtype.val ⁻¹' Kᶜ) q : Type) ≃ₗ[R]
    ReducedSingularHomology R ↥(Kᶜ) (q - 1) := by sorry

/-- Specialisation of `les_boundary_iso_of_acyclic_ambient` to Euclidean space, whose
reduced homology vanishes in every degree. -/
noncomputable def les_boundary_iso_from_acyclicity
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (q : ℕ) :
    (relativeSingularHomology R (↥((∅ : Set (EuclideanSpace ℝ (Fin n)))ᶜ))
      (Subtype.val ⁻¹' Kᶜ) q : Type) ≃ₗ[R]
    ReducedSingularHomology R ↥(Kᶜ) (q - 1) :=
  les_boundary_iso_of_acyclic_ambient R K hK q
    (fun q => euclideanSpace_reduced_homology_vanishes R q)

/-- Edge case of Alexander duality when `q > n`: both sides vanish, so an isomorphism
between them exists trivially. -/
noncomputable def alexander_duality_edge_case
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (q : ℕ) (hqn : n < q) :
    (cechCohomology R (EuclideanSpace ℝ (Fin n)) K ∅ (n - q) : Type) ≃ₗ[R]
    ReducedSingularHomology R ↥(Kᶜ) (q - 1) := by sorry

/-- Alexander duality (Theorem 38.4): for a compact subset `K` of `ℝⁿ`, the composite of
the Poincaré duality cap product and the long exact sequence boundary gives an
isomorphism `Ȟ^{n-q}(K; R) ≅ \widetilde H_{q-1}(ℝⁿ \ K; R)`. -/
noncomputable def alexander_duality
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (q : ℕ) :
    (cechCohomology R (EuclideanSpace ℝ (Fin n)) K ∅ (n - q) : Type) ≃ₗ[R]
    ReducedSingularHomology R ↥(Kᶜ) (q - 1) :=
  haveI := euclideanSpace_isROrientedAlong R K
  if hqn : q ≤ n then

    let pdIso := fullyRelativeCapProductIso R n (EuclideanSpace ℝ (Fin n)) K ∅
      (Set.empty_subset K) hK isCompact_empty (n - q) q (Nat.sub_add_cancel hqn)
    pdIso.toLinearEquiv.trans (les_boundary_iso_from_acyclicity R K hK q)
  else

    alexander_duality_edge_case R K hK q (Nat.lt_of_not_le hqn)

/-- The main range of Alexander duality (`q ≤ n`) extracted as a separate construction
that avoids case-splitting on `q vs n`. -/
noncomputable def alexander_duality_equiv
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (q : ℕ) (hqn : q ≤ n) :
    (cechCohomology R (EuclideanSpace ℝ (Fin n)) K ∅ (n - q) : Type) ≃ₗ[R]
    ReducedSingularHomology R ↥(Kᶜ) (q - 1) :=
  haveI := euclideanSpace_isROrientedAlong R K
  let pdIso := fullyRelativeCapProductIso R n (EuclideanSpace ℝ (Fin n)) K ∅
    (Set.empty_subset K) hK isCompact_empty (n - q) q (Nat.sub_add_cancel hqn)
  pdIso.toLinearEquiv.trans (les_boundary_iso_from_acyclicity R K hK q)


/-- Convenient `Type` view of singular cohomology `H^p(M; R)`, defined here as the
relative cohomology against the empty pair. -/
abbrev singularCohomologyType
    (M : Type) [TopologicalSpace M] (p : ℕ) : Type :=
  (relativeSingularCohomology R M ∅ p : Type)

/-- Convenient `Type` view of singular homology `H_q(M; R)`, defined here as the
relative homology against the empty pair. -/
abbrev singularHomologyType (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (q : ℕ) : Type :=
  (relativeSingularHomology R M ∅ q : Type)

/-- Bridge equivalence between the relative cohomology against the empty pair and the
absolute singular cohomology object used elsewhere in the library. -/
noncomputable def cohomologyBridgeEquiv (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (n : ℕ) :
    singularCohomologyType R M n ≃ₗ[R]
    (SingularCohomology.singularCohomology R (TopCat.of M) (ModuleCat.of R R) n : Type) := by sorry

/-- Bridge equivalence between the relative homology against the empty pair and the
absolute singular homology module used elsewhere in the library. -/
noncomputable def homologyBridgeEquiv (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (n : ℕ) :
    singularHomologyType R M n ≃ₗ[R]
    (SingularCohomology.singularHomologyModule R (TopCat.of M) n : Type) := by sorry

/-- The absolute cup product on singular cohomology, transported via the bridge
equivalences to `singularCohomologyType`. -/
noncomputable def cupProductAbsolute
    (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (p q : ℕ) :
    singularCohomologyType R M p →ₗ[R]
    singularCohomologyType R M q →ₗ[R]
    singularCohomologyType R M (p + q) :=
  ((CapProduct.cupProduct R (TopCat.of M) p q).compl₁₂
    (cohomologyBridgeEquiv R M p).toLinearMap
    (cohomologyBridgeEquiv R M q).toLinearMap).compr₂
    (cohomologyBridgeEquiv R M (p + q)).symm.toLinearMap

/-- The absolute Kronecker pairing `H^n(M; R) × H_n(M; R) → R` transported via the
bridge equivalences. -/
noncomputable def kroneckerPairingAbsolute
    (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (n : ℕ) :
    singularCohomologyType R M n →ₗ[R]
    singularHomologyType R M n →ₗ[R] R :=
  (CapProduct.kroneckerPairing R (TopCat.of M) n).compl₁₂
    (cohomologyBridgeEquiv R M n).toLinearMap
    (homologyBridgeEquiv R M n).toLinearMap

/-- The fundamental class `[M] ∈ H_n(M; R)` of a compact `R`-oriented `n`-manifold,
chosen via the existence statement `fundamentalClass_of_isROrientable`. -/
noncomputable def fundamentalClass
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] :
    singularHomologyType R M n :=
  (fundamentalClass_of_isROrientable R n M (IsROriented.isROrientable (R := R))).choose

/-- The raw cup-product pairing `H^p(M; R) × H^q(M; R) → R`, defined by
`a ⊗ b ↦ ⟨a ∪ b, [M]⟩`, before quotienting by torsion. -/
noncomputable def cupProductPairingRaw
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    singularCohomologyType R M p →ₗ[R]
    singularCohomologyType R M q →ₗ[R] R :=
  let μ : singularHomologyType R M n := fundamentalClass R n M
  let μ' : singularHomologyType R M (p + q) := hpq ▸ μ
  let kron : singularCohomologyType R M (p + q) →ₗ[R] R :=
    (kroneckerPairingAbsolute R M (p + q)).flip μ'
  LinearMap.compr₂ (cupProductAbsolute R M p q) kron

/-- The raw cup-product pairing kills torsion on the left: torsion classes in
`H^p(M; R)` lie in the left kernel of the pairing. -/
theorem cupProductPairingRaw_torsion_left
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    Submodule.torsion R (singularCohomologyType R M p) ≤
      (cupProductPairingRaw R n M p q hpq).ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  ext b
  simp only [LinearMap.zero_apply]
  obtain ⟨⟨r, hr⟩, hra⟩ := ha
  have h1 : r • (cupProductPairingRaw R n M p q hpq a b) =
      cupProductPairingRaw R n M p q hpq (r • a) b := by
    show r • ((cupProductPairingRaw R n M p q hpq) a) b =
      ((cupProductPairingRaw R n M p q hpq) (r • a)) b
    rw [map_smul, LinearMap.smul_apply]
  rw [show (r : R) • a = 0 from hra, map_zero, LinearMap.zero_apply] at h1
  exact hr.1 _ h1

/-- The raw cup-product pairing kills torsion on the right: torsion classes in
`H^q(M; R)` lie in the right kernel of the pairing. -/
theorem cupProductPairingRaw_torsion_right
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    Submodule.torsion R (singularCohomologyType R M q) ≤
      (cupProductPairingRaw R n M p q hpq).flip.ker := by
  intro b hb
  rw [LinearMap.mem_ker]
  ext a
  simp only [LinearMap.zero_apply, LinearMap.flip_apply]
  obtain ⟨⟨r, hr⟩, hrb⟩ := hb
  have h1 : r • (cupProductPairingRaw R n M p q hpq a b) =
      cupProductPairingRaw R n M p q hpq a (r • b) := by
    show r • ((cupProductPairingRaw R n M p q hpq) a) b =
      ((cupProductPairingRaw R n M p q hpq) a) (r • b)
    rw [map_smul]
  rw [show (r : R) • b = 0 from hrb, map_zero] at h1
  exact hr.1 _ h1

/-- The cup-product pairing descended modulo torsion: it induces a pairing on
`H^p(M; R)/tors × H^q(M; R)/tors → R` over any PID `R`. This is the pairing that
appears in Theorem 38.8. -/
noncomputable def cupProductPairingModTorsion (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    ((singularCohomologyType R M p) ⧸
      Submodule.torsion R (singularCohomologyType R M p)) →ₗ[R]
    ((singularCohomologyType R M q) ⧸
      Submodule.torsion R (singularCohomologyType R M q)) →ₗ[R] R :=
  LinearMap.liftQ₂
    (Submodule.torsion R (singularCohomologyType R M p))
    (Submodule.torsion R (singularCohomologyType R M q))
    (cupProductPairingRaw R n M p q hpq)
    (cupProductPairingRaw_torsion_left R n M p q hpq)
    (cupProductPairingRaw_torsion_right R n M p q hpq)

/-- Perfect pairings are preserved under post-composition on the right by a linear
equivalence: if `p : M × N → R` is a perfect pairing and `e : N' ≃ N`, then
`p.compl₂ e` is also a perfect pairing. -/
theorem isPerfPair_compl₂ {R M N N' : Type*}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R N] [Module R N']
    (p : M →ₗ[R] N →ₗ[R] R) (e : N' ≃ₗ[R] N)
    [hp : p.IsPerfPair] : (p.compl₂ e.toLinearMap).IsPerfPair where
  bijective_left := by
    have hbij : Function.Bijective p := hp.bijective_left
    have heq : ⇑(p.compl₂ e.toLinearMap) = (fun f : N →ₗ[R] R => f.comp e.toLinearMap) ∘ p := by
      ext m n'; simp [LinearMap.compl₂_apply]
    rw [heq]
    apply Function.Bijective.comp
    · constructor
      · intro f g h
        ext n
        have := LinearMap.ext_iff.mp h (e.symm n)
        simp at this
        exact this
      · intro f
        exact ⟨f.comp e.symm.toLinearMap, by ext n'; simp⟩
    · exact hbij
  bijective_right := by
    have hbij : Function.Bijective p.flip := hp.bijective_right
    have heq : ⇑((p.compl₂ e.toLinearMap).flip) = p.flip ∘ e := by
      ext n' m; simp [LinearMap.flip_apply, LinearMap.compl₂_apply]
    rw [heq]
    exact hbij.comp e.bijective

/-- The Kronecker pairing kills torsion on the cohomology side: torsion classes in
`H^p(M; R)` lie in the left kernel of the Kronecker pairing. -/
theorem kroneckerPairingAbsolute_torsion_left
    (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (p : ℕ) :
    Submodule.torsion R (singularCohomologyType R M p) ≤
      (kroneckerPairingAbsolute R M p).ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  ext b
  simp only [LinearMap.zero_apply]
  obtain ⟨⟨r, hr⟩, hra⟩ := ha
  have h1 : r • (kroneckerPairingAbsolute R M p a b) =
      kroneckerPairingAbsolute R M p (r • a) b := by
    show r • ((kroneckerPairingAbsolute R M p) a) b =
      ((kroneckerPairingAbsolute R M p) (r • a)) b
    rw [map_smul, LinearMap.smul_apply]
  rw [show (r : R) • a = 0 from hra, map_zero, LinearMap.zero_apply] at h1
  exact hr.1 _ h1

/-- The Kronecker pairing kills torsion on the homology side: torsion classes in
`H_p(M; R)` lie in the right kernel of the Kronecker pairing. -/
theorem kroneckerPairingAbsolute_torsion_right
    (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (p : ℕ) :
    Submodule.torsion R (singularHomologyType R M p) ≤
      (kroneckerPairingAbsolute R M p).flip.ker := by
  intro b hb
  rw [LinearMap.mem_ker]
  ext a
  simp only [LinearMap.zero_apply, LinearMap.flip_apply]
  obtain ⟨⟨r, hr⟩, hrb⟩ := hb
  have h1 : r • (kroneckerPairingAbsolute R M p a b) =
      kroneckerPairingAbsolute R M p a (r • b) := by
    show r • ((kroneckerPairingAbsolute R M p) a) b =
      ((kroneckerPairingAbsolute R M p) a) (r • b)
    rw [map_smul]
  rw [show (r : R) • b = 0 from hrb, map_zero] at h1
  exact hr.1 _ h1

/-- The Kronecker pairing descended modulo torsion on both sides, yielding a pairing
`H^p(M; R)/tors × H_p(M; R)/tors → R` over a PID. -/
noncomputable def kroneckerPairingModTorsion
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (M : Type) [TopologicalSpace M] (p : ℕ) :
    (singularCohomologyType R M p ⧸
      Submodule.torsion R (singularCohomologyType R M p)) →ₗ[R]
    (singularHomologyType R M p ⧸
      Submodule.torsion R (singularHomologyType R M p)) →ₗ[R] R :=
  LinearMap.liftQ₂
    (Submodule.torsion R (singularCohomologyType R M p))
    (Submodule.torsion R (singularHomologyType R M p))
    (kroneckerPairingAbsolute R M p)
    (kroneckerPairingAbsolute_torsion_left R M p)
    (kroneckerPairingAbsolute_torsion_right R M p)

/-- Over a PID, every element of `Ext^1_R(A, R)` is torsion: for each `x` there is a
nonzero `r ∈ R` with `r • x = 0`. This is used in the universal coefficient argument
behind the Poincaré duality / Kronecker pairing modulo torsion. -/
theorem ext1_isTorsion_over_PID
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (A : ModuleCat.{0} R) :
    ∀ x : ((Ext R (ModuleCat.{0} R) 1).obj (Opposite.op A)).obj (ModuleCat.of R R),
      ∃ (r : R), r ≠ 0 ∧ r • x = 0 := by sorry

/-- Over a PID and on a compact `R`-oriented manifold, the absolute Kronecker map
`H^p(M; R) → Hom(H_p(M; R), R)` is surjective. -/
theorem kroneckerPairingAbsolute_surjective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    Function.Surjective (kroneckerPairingAbsolute R M p) := by sorry

/-- Over a PID and on a compact `R`-oriented manifold, the kernel of the absolute
Kronecker map equals exactly the torsion of `H^p(M; R)`. -/
theorem kroneckerPairingAbsolute_ker_le_torsion
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    (kroneckerPairingAbsolute R M p).ker ≤
      Submodule.torsion R (singularCohomologyType R M p) := by sorry

/-- The Kronecker pairing modulo torsion is surjective onto
`Hom(H_p(M; R)/tors, R)`. -/
theorem kroneckerPairingModTorsion_surjective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    Function.Surjective (kroneckerPairingModTorsion R M p) := by sorry

/-- The Kronecker pairing modulo torsion is bijective: it identifies `H^p(M; R)/tors`
with the dual of `H_p(M; R)/tors`. -/
theorem kroneckerPairingModTorsion_bijective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    Function.Bijective (kroneckerPairingModTorsion R M p) := by
  refine ⟨?_, kroneckerPairingModTorsion_surjective R n M p⟩
  intro a b hab
  obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  apply kroneckerPairingAbsolute_ker_le_torsion R n M p
  rw [LinearMap.mem_ker]
  ext x
  simp only [LinearMap.zero_apply]
  have heq := congr_fun (congr_arg DFunLike.coe hab) (Submodule.Quotient.mk x)
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact heq

/-- The Kronecker pairing modulo torsion packaged as a linear equivalence
`H^p(M; R)/tors ≃ₗ Hom(H_p(M; R)/tors, R)`. -/
noncomputable def kroneckerPairingModTorsion_equiv
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    (singularCohomologyType R M p ⧸
      Submodule.torsion R (singularCohomologyType R M p)) ≃ₗ[R]
    ((singularHomologyType R M p ⧸
      Submodule.torsion R (singularHomologyType R M p)) →ₗ[R] R) :=
  LinearEquiv.ofBijective (kroneckerPairingModTorsion R M p)
    (kroneckerPairingModTorsion_bijective R n M p)

/-- The underlying function of `kroneckerPairingModTorsion_equiv` is just the
Kronecker pairing modulo torsion. -/
theorem kroneckerPairingModTorsion_equiv_eq
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    ⇑(kroneckerPairingModTorsion_equiv R n M p) =
      ⇑(kroneckerPairingModTorsion R M p) := by
  funext a
  exact LinearEquiv.ofBijective_apply (kroneckerPairingModTorsion R M p) a

/-- On a compact `R`-oriented manifold over a PID, the torsion-free quotient of singular
homology `H_p(M; R)/tors` is a reflexive `R`-module. -/
theorem singularHomologyModTorsion_isReflexive
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    Module.IsReflexive R (singularHomologyType R M p ⧸
      Submodule.torsion R (singularHomologyType R M p)) := by sorry

/-- The "flipped" version of `kroneckerPairingModTorsion_equiv`, identifying
`H_p(M; R)/tors` with the dual of `H^p(M; R)/tors` using reflexivity. -/
noncomputable def kroneckerPairingModTorsion_equiv_flip
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    (singularHomologyType R M p ⧸
      Submodule.torsion R (singularHomologyType R M p)) ≃ₗ[R]
    ((singularCohomologyType R M p ⧸
      Submodule.torsion R (singularCohomologyType R M p)) →ₗ[R] R) :=
  haveI := singularHomologyModTorsion_isReflexive R n M p
  (kroneckerPairingModTorsion_equiv R n M p).flip

/-- The underlying function of the flipped Kronecker equivalence equals the flipped
Kronecker pairing modulo torsion. -/
theorem kroneckerPairingModTorsion_equiv_flip_eq
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    ⇑(kroneckerPairingModTorsion_equiv_flip R n M p) =
      ⇑((kroneckerPairingModTorsion R M p).flip) := by sorry

/-- The Kronecker pairing modulo torsion is a perfect pairing on a compact `R`-oriented
manifold over a PID. -/
theorem kroneckerPairingModTorsion_isPerfPair
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] (p : ℕ) :
    (kroneckerPairingModTorsion R M p).IsPerfPair := by
  constructor
  ·
    rw [show ⇑(kroneckerPairingModTorsion R M p) =
      ⇑(kroneckerPairingModTorsion_equiv R n M p) from
      (kroneckerPairingModTorsion_equiv_eq R n M p).symm]
    exact (kroneckerPairingModTorsion_equiv R n M p).bijective
  ·
    rw [show ⇑(kroneckerPairingModTorsion R M p).flip =
      ⇑(kroneckerPairingModTorsion_equiv_flip R n M p) from
      (kroneckerPairingModTorsion_equiv_flip_eq R n M p).symm]
    exact (kroneckerPairingModTorsion_equiv_flip R n M p).bijective

/-- Poincaré duality descended modulo torsion: an `R`-linear equivalence
`H^q(M; R)/tors ≃ₗ H_p(M; R)/tors` for `p + q = n` on a compact `R`-oriented manifold. -/
noncomputable def poincareDuality_modTorsion_equiv
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    (singularCohomologyType R M q ⧸
      Submodule.torsion R (singularCohomologyType R M q)) ≃ₗ[R]
    (singularHomologyType R M p ⧸
      Submodule.torsion R (singularHomologyType R M p)) :=
  let e := (poincareDualityIso R n M q p (by linarith)).toLinearEquiv
  Submodule.Quotient.equiv
    (Submodule.torsion R (singularCohomologyType R M q))
    (Submodule.torsion R (singularHomologyType R M p))
    e
    (by
      ext x
      simp only [Submodule.mem_map, Submodule.mem_torsion'_iff]
      constructor
      · rintro ⟨y, ⟨a, ha⟩, rfl⟩
        exact ⟨a, by
          show (a : R) • e y = 0
          rw [← e.map_smul]
          show e ((a : R) • y) = 0
          have : (a : R) • y = 0 := ha
          rw [this, map_zero]⟩
      · intro ⟨a, ha⟩
        refine ⟨e.symm x, ⟨a, ?_⟩, e.apply_symm_apply x⟩
        show (a : R) • e.symm x = 0
        rw [← e.symm.map_smul]
        show e.symm ((a : R) • x) = 0
        have : (a : R) • x = 0 := ha
        rw [this, map_zero])


/-- Compatibility of the Poincaré duality isomorphism with the cohomology/homology
bridge equivalences: applying the bridge map after Poincaré duality equals capping
with the (transported) fundamental class. -/
theorem poincareDualityIso_bridge_compat
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) (hqp : q + p = n := by omega)
    (b : singularCohomologyType R M q) :
    (homologyBridgeEquiv R M p)
      ((poincareDualityIso R n M q p (show q + p = n from hqp)).toLinearEquiv b) =
    CapProduct.capProduct R (TopCat.of M) q p
      (cohomologyBridgeEquiv R M q b)
      ((Nat.add_comm p q) ▸
        (homologyBridgeEquiv R M (p + q) (hpq ▸ fundamentalClass R n M))) := by sorry

/-- The cup–cap identity at the raw (pre-quotient) level:
`⟨a ∪ b, [M]⟩ = ⟨a, PD(b)⟩`, expressing the cup-product pairing as the Kronecker
pairing composed with Poincaré duality. -/
theorem cupCapIdentityRaw
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n)
    (a : singularCohomologyType R M p)
    (b : singularCohomologyType R M q) :
    cupProductPairingRaw R n M p q hpq a b =
      kroneckerPairingAbsolute R M p a
        ((poincareDualityIso R n M q p (by linarith)).toLinearEquiv b) := by


  show (LinearMap.compr₂ (cupProductAbsolute R M p q)
    ((kroneckerPairingAbsolute R M (p + q)).flip (hpq ▸ fundamentalClass R n M))) a b =
    kroneckerPairingAbsolute R M p a
      ((poincareDualityIso R n M q p (by linarith)).toLinearEquiv b)
  simp only [LinearMap.compr₂_apply, LinearMap.flip_apply]

  simp only [kroneckerPairingAbsolute, cupProductAbsolute,
    LinearMap.compl₁₂_apply, LinearMap.compr₂_apply]


  have hcancel : ∀ (x : (SingularCohomology.singularCohomology R (TopCat.of M)
      (ModuleCat.of R R) (p + q) : Type)),
    (cohomologyBridgeEquiv R M (p + q)) ((cohomologyBridgeEquiv R M (p + q)).symm x) = x :=
    fun x => (cohomologyBridgeEquiv R M (p + q)).apply_symm_apply x
  erw [hcancel]


  have h34 := CapProduct.kronecker_cup_eq_kronecker_cap R (TopCat.of M) p q
    ((cohomologyBridgeEquiv R M p) a)
    ((cohomologyBridgeEquiv R M q) b)
    ((homologyBridgeEquiv R M (p + q)) (hpq ▸ fundamentalClass R n M))
  erw [h34]

  congr 1


  exact (poincareDualityIso_bridge_compat R n M p q hpq (by omega) b).symm

/-- The cup-product pairing modulo torsion equals the Kronecker pairing composed with
Poincaré duality (modulo torsion), `pair_cup = pair_kron ∘ PD`. -/
theorem cupProductPairing_eq_kronecker_comp_PD
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    cupProductPairingModTorsion R n M p q hpq =
      (kroneckerPairingModTorsion R M p).compl₂
        (poincareDuality_modTorsion_equiv R n M p q hpq).toLinearMap := by
  ext a b
  show cupProductPairingRaw R n M p q hpq a b =
    kroneckerPairingAbsolute R M p a
      ((poincareDualityIso R n M q p (by linarith)).toLinearEquiv b)
  exact cupCapIdentityRaw R n M p q hpq a b

/-- The cup-product pairing modulo torsion factors as `pair.compl₂ e` for some perfect
pairing `pair` and linear equivalence `e`. This is the structural fact used to deduce
that the cup-product pairing itself is perfect. -/
theorem cupProductPairing_factorsAsPerfPairCompl₂
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module R N)
      (pairing : (singularCohomologyType R M p ⧸
        Submodule.torsion R (singularCohomologyType R M p)) →ₗ[R] N →ₗ[R] R)
      (_ : pairing.IsPerfPair)
      (e : ((singularCohomologyType R M q) ⧸
              Submodule.torsion R (singularCohomologyType R M q)) ≃ₗ[R] N),
      cupProductPairingModTorsion R n M p q hpq = pairing.compl₂ e.toLinearMap := by
  refine ⟨singularHomologyType R M p ⧸ Submodule.torsion R (singularHomologyType R M p),
    inferInstance, inferInstance,
    kroneckerPairingModTorsion R M p,
    kroneckerPairingModTorsion_isPerfPair R n M p,
    poincareDuality_modTorsion_equiv R n M p q hpq,
    cupProductPairing_eq_kronecker_comp_PD R n M p q hpq⟩

/-- Theorem 38.8 (perfect-pairing form of Poincaré duality): for a compact `R`-oriented
`n`-manifold `M` over a PID `R`, the cup-product pairing
`H^p(M; R)/tors × H^q(M; R)/tors → R` (with `p + q = n`) is a perfect pairing. -/
theorem cupProductPairingModTorsion_isPerfPair
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    (cupProductPairingModTorsion R n M p q hpq).IsPerfPair := by

  obtain ⟨N, instAG, instMod, pairing, hperf, e, heq⟩ :=
    cupProductPairing_factorsAsPerfPairCompl₂ R n M p q hpq

  letI := instAG
  letI := instMod
  letI := hperf

  rw [heq]

  exact isPerfPair_compl₂ pairing e

end PoincareDuality

namespace AlexanderDuality

open PoincareDuality

/-- The reduced singular homology `\widetilde H_{-1}(Kᶜ; R)` — interpreted via natural
subtraction `0 - 1 = 0` and the augmentation kernel definition — is trivial. -/
theorem reducedSingularHomology_neg_one_subsingleton
    (R : Type) [CommRing R]
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) :
    Subsingleton (ReducedSingularHomology R ↥(Kᶜ) ((0 : ℕ) - 1)) := by sorry

/-- The relative singular homology `H_0(ℝⁿ, ℝⁿ \ K; R)` vanishes, used as a stepping
stone to deduce vanishing of top-degree Čech cohomology of `K`. -/
theorem relativeSingularHomology_degree_zero_subsingleton_of_acyclic
    (R : Type) [CommRing R]
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) :
    Subsingleton (relativeSingularHomology R (↥((∅ : Set (EuclideanSpace ℝ (Fin n)))ᶜ))
      (Subtype.val ⁻¹' Kᶜ) 0 : Type) := by

  have lesIso := les_boundary_iso_from_acyclicity R K hK 0

  haveI : Subsingleton (ReducedSingularHomology R ↥(Kᶜ) ((0 : ℕ) - 1)) :=
    reducedSingularHomology_neg_one_subsingleton R K hK

  exact Subsingleton.intro (fun a b => lesIso.injective (Subsingleton.elim _ _))

/-- Corollary 38.5: for a compact subset `K` of `ℝⁿ`, the Čech cohomology
`Ȟ^n(K; R)` vanishes. -/
theorem cechCohomology_compact_euclidean_top_degree_eq_zero
    (R : Type) [CommRing R]
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) :
    Subsingleton (cechCohomology R (EuclideanSpace ℝ (Fin n)) K ∅ n : Type) := by

  haveI := euclideanSpace_isROrientedAlong R K
  have pdIso := fullyRelativeCapProductIso R n (EuclideanSpace ℝ (Fin n)) K ∅
    (Set.empty_subset K) hK isCompact_empty n 0 (by omega)

  haveI := relativeSingularHomology_degree_zero_subsingleton_of_acyclic R K hK

  exact Subsingleton.intro (fun a b => by
    have heq : pdIso.toLinearEquiv a = pdIso.toLinearEquiv b := Subsingleton.elim _ _
    exact pdIso.toLinearEquiv.injective heq)

/-- Auxiliary Jordan–Brouwer separation statement: a compact subset `K` of `ℝⁿ`
(`n ≥ 1`) homeomorphic to the unit sphere `Sⁿ⁻¹`-style sphere has complement with
exactly two connected components. -/
theorem jordan_brouwer_separation_aux
    {n : ℕ} (hn : n ≥ 1)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hHomeo : Nonempty (↥K ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) :
    Nat.card (ConnectedComponents ↥Kᶜ) = 2 := by sorry

end AlexanderDuality

open CategoryTheory AlgebraicTopology Limits TopCat

namespace AlgebraicTopologyI

/-- A knot is a topological embedding `S¹ ↪ S³`. -/
def IsKnot (f : (𝕊 1 : TopCat.{0}) ⟶ (𝕊 3 : TopCat.{0})) : Prop :=
  Topology.IsEmbedding f

/-- The complement `S³ \ f(S¹)` of a knot `f : S¹ ↪ S³`, packaged as a topological
space. -/
def knotComplement (f : (𝕊 1 : TopCat.{0}) ⟶ (𝕊 3 : TopCat.{0})) : TopCat.{0} :=
  TopCat.of { x : (𝕊 3 : TopCat.{0}) | x ∉ Set.range f }

/-- A space `X` is a homology circle if its singular homology agrees with that of the
circle `S¹` in every degree and over every commutative ring `R`. -/
def IsHomologyCircle (X : TopCat.{0}) : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    Nonempty (SingularCohomology.singularHomologyModule R X n ≅
              SingularCohomology.singularHomologyModule R (𝕊 1 : TopCat.{0}) n)

/-- Corollary 38.6: the complement of a knot in `S³` is a homology circle. -/
theorem knotComplement_isHomologyCircle
    (f : (𝕊 1 : TopCat.{0}) ⟶ (𝕊 3 : TopCat.{0})) (hf : IsKnot f) :
    IsHomologyCircle (knotComplement f) := by sorry


end AlgebraicTopologyI

end
