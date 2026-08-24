/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order

noncomputable section

namespace Lec22

open MvPolynomial

/-- The number of monomials of degree `d` in `n + 1` variables, equal to `choose (n + d) d`. -/
def veroneseMonomialCount (n d : ℕ) : ℕ := Nat.choose (n + d) d

/-- The dimension `N` of the projective target of the degree-`d` Veronese embedding
of `ℙⁿ`, equal to `choose (n + d) d - 1`. -/
def veroneseTargetDim (n d : ℕ) : ℕ := veroneseMonomialCount n d - 1

/-- Smoothness of the projective hypersurface `V(f) ⊆ ℙⁿ`: at every nonzero point where
`f` vanishes, some partial derivative of `f` is nonzero (Jacobian criterion). -/
def IsSmooth_Hypersurface (k : Type*) [CommRing k] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) k) : Prop :=
  ∀ x : Fin (n + 1) → k,
    (∃ i, x i ≠ 0) →
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

/-- Combinatorial proxy for a smooth projective subvariety of `ℙⁿ`: a set of defining
polynomials, the nonzero points on the variety, and the smoothness/dimension data. -/
structure SmoothProjVariety (k : Type*) [CommRing k] (n : ℕ) where
  definingPolys : Set (MvPolynomial (Fin (n + 1)) k)
  points : Set (Fin (n + 1) → k)
  points_nonzero : ∀ x ∈ points, ∃ i : Fin (n + 1), x i ≠ 0
  points_vanish : ∀ x ∈ points, ∀ f ∈ definingPolys, MvPolynomial.eval x f = 0
  dim : ℕ
  smooth : ∀ x ∈ points, ∀ g ∈ definingPolys,
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i g) ≠ 0

/-- The hypersurface `V(f)` cuts `X` transversally: at every point of `X` where `f`
vanishes, some partial derivative of `f` is nonzero. -/
def IsSmooth_Intersection (k : Type*) [CommRing k] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) k)
    (X : SmoothProjVariety k n) : Prop :=
  ∀ x ∈ X.points,
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

/-- The Zariski topology on the parameter space of degree-`d` hypersurfaces in `ℙⁿ`,
used to formulate "generic" properties. -/
noncomputable def zariskiTopologyHypersurfaces (k : Type*) [Field k] (n d : ℕ) :
    TopologicalSpace (MvPolynomial (Fin (n + 1)) k) := by sorry

/-- A property `P` of degree-`d` hypersurfaces holds generically if there is a nonempty
Zariski-open (and dense) subset of the parameter space on which `P` holds. -/
def IsGenericProperty (k : Type*) [Field k] (n d : ℕ)
    (P : MvPolynomial (Fin (n + 1)) k → Prop) : Prop :=
  let _ := zariskiTopologyHypersurfaces k n d
  ∃ U : Set (MvPolynomial (Fin (n + 1)) k),
    IsOpen U ∧ Dense U ∧ ∀ f ∈ U, P f

/-- Bertini for hyperplane sections: For a smooth projective variety `Y ⊆ ℙᴺ` over an
algebraically closed field, the generic hyperplane section is smooth. -/
theorem bertini_hyperplane_smooth
    (k : Type*) [Field k] [IsAlgClosed k]
    (N : ℕ) (hN : 0 < N)
    (Y : SmoothProjVariety k N) :
    IsGenericProperty k N 1 (fun ℓ => IsSmooth_Intersection k N ℓ Y) := by sorry

/-- The degree-`d` Veronese embedding `ℙⁿ ↪ ℙᴺ` carries a smooth projective variety to
a smooth projective variety, allowing degree-`d` hypersurfaces in `ℙⁿ` to be related to
hyperplane sections in `ℙᴺ`. -/
noncomputable def veronese_preserves_smoothness
    (k : Type*) [Field k] (n d : ℕ) (hd : 0 < d)
    (X : SmoothProjVariety k n) :
    SmoothProjVariety k (veroneseTargetDim n d) := by sorry

/-- Genericity of smooth hyperplane sections of the Veronese image transfers back to
genericity of smooth degree-`d` hypersurfaces of the original variety. -/
theorem veronese_transfers_genericity
    (k : Type*) [Field k] [IsAlgClosed k]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (X : SmoothProjVariety k n)
    (Y : SmoothProjVariety k (veroneseTargetDim n d))
    (hY : Y = veronese_preserves_smoothness k n d hd X)
    (hBertini : IsGenericProperty k (veroneseTargetDim n d) 1
      (fun ℓ => IsSmooth_Intersection k (veroneseTargetDim n d) ℓ Y)) :
    IsGenericProperty k n d (fun f => IsSmooth_Intersection k n f X) := by sorry

/-- The projective space `ℙⁿ` itself, viewed as the trivial smooth projective variety
with no defining equations. -/
def smoothProjSpace (k : Type*) [CommRing k] (n : ℕ) : SmoothProjVariety k n where
  definingPolys := ∅
  points := { x | ∃ i : Fin (n + 1), x i ≠ 0 }
  points_nonzero := fun _ hx => hx
  points_vanish := fun _ _ _ hf => absurd hf (Set.notMem_empty _)
  dim := n
  smooth := fun _ _ _ hg => absurd hg (Set.notMem_empty _)

/-- For positive `n` and `d`, the Veronese target dimension is strictly positive. -/
lemma veroneseTargetDim_pos (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    0 < veroneseTargetDim n d := by
  unfold veroneseTargetDim veroneseMonomialCount
  have h1 : Nat.choose (n + 1) n = n + 1 := Nat.choose_succ_self_right n
  have h2 : Nat.choose (n + 1) n ≤ Nat.choose (n + d) n :=
    Nat.choose_le_choose n (by omega)
  have h3 : Nat.choose (n + d) n = Nat.choose (n + d) d := by
    have := Nat.choose_symm (show n ≤ n + d by omega)
    have hnd : n + d - n = d := by omega
    rw [hnd] at this; exact this.symm
  omega

/-- Corollary 28 (generic smooth hypersurface): Over an algebraically closed field,
a generic degree-`d` hypersurface in `ℙⁿ` is smooth. -/
theorem corollary28_generic_smooth_hypersurface
    (k : Type*) [Field k] [IsAlgClosed k]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    IsGenericProperty k n d (IsSmooth_Hypersurface k n) := by

  let Pn := smoothProjSpace k n

  let N := veroneseTargetDim n d
  have hN : 0 < N := veroneseTargetDim_pos n d hn hd
  let Vn := veronese_preserves_smoothness k n d hd Pn

  have hBertini := bertini_hyperplane_smooth k N hN Vn

  have hTransfer := veronese_transfers_genericity k n d hn hd Pn Vn rfl hBertini


  obtain ⟨U, hUopen, hUdense, hU⟩ := hTransfer
  exact ⟨U, hUopen, hUdense, fun f hf x hx hfx => hU f hf x hx hfx⟩

/-- Corollary 28 (generic smooth intersection): Over an algebraically closed field, for any
smooth projective variety `X ⊆ ℙⁿ`, a generic degree-`d` hypersurface cuts `X` smoothly. -/
theorem corollary28_generic_smooth_intersection
    (k : Type*) [Field k] [IsAlgClosed k]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (X : SmoothProjVariety k n) :
    IsGenericProperty k n d (fun f => IsSmooth_Intersection k n f X) := by


  let N := veroneseTargetDim n d
  have hN : 0 < N := veroneseTargetDim_pos n d hn hd
  let Vx := veronese_preserves_smoothness k n d hd X

  have hBertini := bertini_hyperplane_smooth k N hN Vx

  exact veronese_transfers_genericity k n d hn hd X Vx rfl hBertini

end Lec22

end
