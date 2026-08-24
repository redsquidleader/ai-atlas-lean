/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section34
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open Set

namespace CechCohomology

/-- A map `φ : J → I` between preorders is **cofinal** if every `i : I` is
$\le$ some `φ j`. Used to recognise when pulling a directed system back along
`φ` gives the same direct limit. -/
def IsCofinalMap {I : Type*} {J : Type*} [LE I] (φ : J → I) : Prop :=
  ∀ i : I, ∃ j : J, i ≤ φ j

section DirectLimits

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [DecidableEq κ] [Nonempty κ]
variable (G : ι → Type*) [∀ i, AddCommGroup (G i)]
variable (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G fun i j h ↦ f i j h]
variable (φ : κ →o ι)

/-- Pullback of the bonding maps of a directed system `(G, f)` along a monotone
map `φ : κ →o ι`: the pulled-back system has fibres `G (φ j)` and bonding maps
`f (φ j₁) (φ j₂) (φ.monotone h)`. -/
def pullbackBondingMap (j₁ j₂ : κ) (h : j₁ ≤ j₂) : G (φ j₁) →+ G (φ j₂) :=
  f (φ j₁) (φ j₂) (φ.monotone h)

/-- The canonical map from the direct limit of the pulled-back system over `κ`
to the direct limit over `ι` of the original system, induced by the universal
property of direct limits. -/
noncomputable def cofinalMap :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) →+
    AddCommGroup.DirectLimit G f :=
  AddCommGroup.DirectLimit.lift _ _ _
    (fun j => AddCommGroup.DirectLimit.of G f (φ j))
    (fun _ _ hij x => AddCommGroup.DirectLimit.of_f (f := f) (φ.monotone hij) x)

/-- **Lemma 35.7 (cofinal maps and direct limits).** If `φ : κ →o ι` is cofinal
(every `i : ι` is `≤ φ j` for some `j : κ`), then the induced map between
direct limits is an additive equivalence: the limit over a cofinal subset
recovers the full limit. -/
noncomputable def cofinalMapEquiv
    (hcof : ∀ i : ι, ∃ j : κ, i ≤ φ j) :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) ≃+
    AddCommGroup.DirectLimit G f :=
  AddEquiv.ofBijective (cofinalMap G f φ)
    ⟨by


      rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [AddMonoidHom.mem_ker] at ha
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih j x =>
        simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of] at ha
        obtain ⟨i, hji, hzero⟩ := AddCommGroup.DirectLimit.of.zero_exact (φ j) x ha
        obtain ⟨j', hij'⟩ := hcof i
        obtain ⟨k, hjk, hj'k⟩ := directed_of (· ≤ ·) j j'
        have h_i_phik : i ≤ φ k := le_trans hij' (φ.monotone hj'k)
        have key : pullbackBondingMap G f φ j k hjk x = 0 := by
          show f (φ j) (φ k) (φ.monotone hjk) x = 0
          rw [show f (φ j) (φ k) (φ.monotone hjk) x =
                f i (φ k) h_i_phik (f (φ j) i hji x) from
            (DirectedSystem.map_map (f := fun i j h ↦ f i j h) hji h_i_phik x).symm]
          rw [hzero, map_zero]
        simp only [AddSubgroup.mem_bot]
        rw [show AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j x =
          AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) k
            (pullbackBondingMap G f φ j k hjk x)
          from (AddCommGroup.DirectLimit.of_f (f := pullbackBondingMap G f φ) hjk x).symm]
        rw [key, map_zero],
    by
      intro a
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih i x =>
        obtain ⟨j, hij⟩ := hcof i
        exact ⟨AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j
          (f i (φ j) hij x), by
          simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of]
          exact AddCommGroup.DirectLimit.of_f (f := f) hij x⟩⟩

end DirectLimits

variable {X : Type*} [TopologicalSpace X]

/-- **Cofinality (left half) of the Mayer–Vietoris diagram.** Given open
neighborhoods `U ⊇ A ∪ B`, `V ⊇ B` with `V ⊆ U`, we can find open
neighborhoods `W` of `A` and `Y` of `B` such that `W ∪ Y ⊆ U` and `Y ⊆ V`
— trivially, take `W := U`, `Y := V`. -/
theorem cofinal_neighborhood_left
    {A B U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hABU : A ∪ B ⊆ U) (hBV : B ⊆ V) (hVU : V ⊆ U) :
    ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
      W ∪ Y ⊆ U ∧ Y ⊆ V :=
  ⟨U, V, hU, hV, subset_union_left.trans hABU, hBV, (union_eq_left.mpr hVU).le, Subset.rfl⟩

omit [TopologicalSpace X] in
/-- Auxiliary set-theoretic lemma: if `S` and `T` are disjoint, then
`(U ∩ S) ∩ (V ∪ T) ⊆ V`. Used to verify the inclusion `W ∩ Y ⊆ V` in the
normal/compact cofinality arguments. -/
theorem inter_inter_union_subset_of_disjoint {U S V T : Set X}
    (hST : Disjoint S T) : (U ∩ S) ∩ (V ∪ T) ⊆ V := by
  intro x hx
  rcases hx.2 with hxV | hxT
  · exact hxV
  · exact (Set.disjoint_iff.mp hST ⟨hx.1.2, hxT⟩).elim

/-- **Cofinality (right half) for a normal space.** Given closed disjoint
`A`, `B` and open `U ⊇ A`, `V ⊇ A ∩ B`, normality produces open `W ⊇ A`,
`Y ⊇ B` with `W ⊆ U` and `W ∩ Y ⊆ V`. Proven by separating `A` from
`B ∩ Vᶜ` via `normal_separation`. -/
theorem cofinal_neighborhood_right_normal [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hABV : A ∩ B ⊆ V) :
    ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
      W ⊆ U ∧ W ∩ Y ⊆ V := by

  have hclosed_BVc : IsClosed (B ∩ Vᶜ) := hB.inter (isClosed_compl_iff.mpr hV)
  have hdisj : Disjoint A (B ∩ Vᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨hxA, hxB, hxV⟩
    exact hxV (hABV ⟨hxA, hxB⟩)

  obtain ⟨S, T, hS, hT, hAS, hBVT, hST⟩ := normal_separation hA hclosed_BVc hdisj

  have hBYT : B ⊆ V ∪ T := by rwa [← compl_compl V, ← Set.inter_subset]

  exact ⟨U ∩ S, V ∪ T, hU.inter hS, hV.union hT,
    subset_inter hAU hAS, hBYT, inter_subset_left,
    inter_inter_union_subset_of_disjoint hST⟩

/-- **Cofinality (right half) for a Hausdorff space.** The compact analogue of
`cofinal_neighborhood_right_normal`: for compact `A`, `B` in a Hausdorff space,
the same separation conclusion holds, using
`SeparatedNhds.of_isCompact_isCompact`. -/
theorem cofinal_neighborhood_right_compact [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hABV : A ∩ B ⊆ V) :
    ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
      W ⊆ U ∧ W ∩ Y ⊆ V := by

  have hcompact_BVc : IsCompact (B ∩ Vᶜ) := hB.inter_right (isClosed_compl_iff.mpr hV)
  have hdisj : Disjoint A (B ∩ Vᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨hxA, hxB, hxV⟩
    exact hxV (hABV ⟨hxA, hxB⟩)

  obtain ⟨S, T, hS, hT, hAS, hBVT, hST⟩ :=
    SeparatedNhds.of_isCompact_isCompact hA hcompact_BVc hdisj

  have hBYT : B ⊆ V ∪ T := by rwa [← compl_compl V, ← Set.inter_subset]

  exact ⟨U ∩ S, V ∪ T, hU.inter hS, hV.union hT,
    subset_inter hAU hAS, hBYT, inter_subset_left,
    inter_inter_union_subset_of_disjoint hST⟩

/-- **Lemma 35.8 (cofinality for Mayer–Vietoris, normal case).** For closed
subsets `A`, `B` of a normal space, the two cofinality conditions
(`cofinal_neighborhood_left` and `cofinal_neighborhood_right_normal`) both
hold; this is the input needed to deduce excision (and hence Mayer–Vietoris)
from the abstract cofinality machinery. -/
theorem neighborhood_maps_cofinal_normal [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    (∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ∪ Y ⊆ U ∧ Y ⊆ V) ∧
    (∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ⊆ U ∧ W ∩ Y ⊆ V) :=
  ⟨fun _ _ hU hV hABU hBV hVU => cofinal_neighborhood_left hU hV hABU hBV hVU,
   fun _ _ hU hV hAU hABV => cofinal_neighborhood_right_normal hA hB hU hV hAU hABV⟩

/-- Compact analogue of `neighborhood_maps_cofinal_normal`: the same conjunction
of cofinality conditions holds for compact subsets of a Hausdorff space. -/
theorem neighborhood_maps_cofinal_compact [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) :
    (∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ∪ Y ⊆ U ∧ Y ⊆ V) ∧
    (∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ⊆ U ∧ W ∩ Y ⊆ V) :=
  ⟨fun _ _ hU hV hABU hBV hVU => cofinal_neighborhood_left hU hV hABU hBV hVU,
   fun _ _ hU hV hAU hABV => cofinal_neighborhood_right_compact hA hB hU hV hAU hABV⟩

end CechCohomology

open CategoryTheory AlgebraicTopology Limits TopologicalSpace Function

noncomputable section

namespace CechCohomology

/-- Exactness is preserved under direct limits of abelian groups: given two
composable, pointwise-exact natural transformations of directed systems of
abelian groups, the induced sequence of direct limits is again exact. -/
theorem addCommGroup_directLimit_map_exact
    {ι : Type*} [DecidableEq ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    {f : ∀ i j, i ≤ j → G i →+ G j} [DirectedSystem G fun i j h ↦ f i j h]
    {G' : ι → Type*} [∀ i, AddCommGroup (G' i)]
    {f' : ∀ i j, i ≤ j → G' i →+ G' j} [DirectedSystem G' fun i j h ↦ f' i j h]
    {G'' : ι → Type*} [∀ i, AddCommGroup (G'' i)]
    {f'' : ∀ i j, i ≤ j → G'' i →+ G'' j} [DirectedSystem G'' fun i j h ↦ f'' i j h]
    (p : ∀ i, G i →+ G' i) (hp : ∀ i j h, (p j).comp (f i j h) = (f' i j h).comp (p i))
    (q : ∀ i, G' i →+ G'' i) (hq : ∀ i j h, (q j).comp (f' i j h) = (f'' i j h).comp (q i))
    (exact_at : ∀ i, Function.Exact (p i) (q i)) :
    Function.Exact
      (AddCommGroup.DirectLimit.map p hp)
      (AddCommGroup.DirectLimit.map q hq) := by
  intro y
  constructor
  · intro hy
    induction y using AddCommGroup.DirectLimit.induction_on with
    | ih i yi =>
      rw [AddCommGroup.DirectLimit.map_apply_of] at hy
      obtain ⟨j, hij, hfq⟩ := AddCommGroup.DirectLimit.of.zero_exact i (q i yi) hy
      have hqf : q j (f' i j hij yi) = 0 := by
        have := DFunLike.congr_fun (hq i j hij) yi
        simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
        rw [this, hfq]
      obtain ⟨xj, hxj⟩ := ((exact_at j) (f' i j hij yi)).mp hqf
      exact ⟨AddCommGroup.DirectLimit.of G f j xj, by
        rw [AddCommGroup.DirectLimit.map_apply_of, hxj,
          AddCommGroup.DirectLimit.of_f]⟩
  · rintro ⟨x, rfl⟩
    induction x using AddCommGroup.DirectLimit.induction_on with
    | ih i xi =>
      simp only [AddCommGroup.DirectLimit.map_apply_of]
      have : q i (p i xi) = 0 := ((exact_at i) (p i xi)).mpr ⟨xi, rfl⟩
      rw [this, map_zero]

/-- The functor sending a space `Y` to its integral singular chain complex
$S_\bullet(Y; \mathbb{Z})$ as a chain complex of `ℤ`-modules. -/
abbrev singChain : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- $p$-th integral singular cohomology $H^p(Y; \mathbb{Z})$ of a space `Y`,
computed by dualising `singChain Y` and taking the `p`-th cohomology. -/
def singCohom (Y : TopCat.{0}) (p : ℕ) : ModuleCat.{0} ℤ :=
  ((singChain.obj Y).linearYonedaObj ℤ (ModuleCat.of ℤ ℤ)).homology p

end CechCohomology

/-- Čech cohomology $\check{H}^p(X, K; \mathbb{Z})$ of a subset `K ⊆ X`,
defined as the direct limit (`cechCohomology`) of singular cohomology over
open neighborhoods of `K`. -/
def CechCohomology.CechCohom
    (X : Type) [TopologicalSpace X] (K : Set X) (p : ℕ) : Type :=
  (CechCohomology.cechCohomology ℤ K p : Type)

/-- The additive group structure on `CechCohom X K p`, inherited from the
underlying module. -/
noncomputable instance CechCohomology.CechCohom.addCommGroup
    (X : Type) [TopologicalSpace X]
    (K : Set X) (p : ℕ) : AddCommGroup (CechCohomology.CechCohom X K p) :=
  (CechCohomology.cechCohomology ℤ K p).isAddCommGroup


/-- The restriction homomorphism $\check{H}^p(X, K) \to \check{H}^p(X, L)$ for
$L \subseteq K$, induced functorially by precomposition with open
neighborhoods. -/
noncomputable def CechCohomology.CechCohom.restrict
    (X : Type) [TopologicalSpace X]
    {K L : Set X} (h : L ⊆ K) (p : ℕ) :
    CechCohomology.CechCohom X K p →+ CechCohomology.CechCohom X L p := by sorry


namespace CechCohomology

open CechCohomology Function

/-- Mayer–Vietoris restriction map: a class on `A ∪ B` restricts to a pair of
classes on `A` and `B`. -/
def mvRestrict (X : Type) [TopologicalSpace X]
    (A B : Set X) (p : ℕ) :
    CechCohom X (A ∪ B) p →+ CechCohom X A p × CechCohom X B p :=
  AddMonoidHom.prod
    (CechCohom.restrict X Set.subset_union_left p)
    (CechCohom.restrict X Set.subset_union_right p)

/-- Mayer–Vietoris difference map: a pair of classes on `A` and `B` produces
the difference of their restrictions to `A ∩ B`. -/
def mvDiff (X : Type) [TopologicalSpace X]
    (A B : Set X) (p : ℕ) :
    CechCohom X A p × CechCohom X B p →+ CechCohom X (A ∩ B) p :=
  (CechCohom.restrict X Set.inter_subset_left p).comp (AddMonoidHom.fst _ _) -
  (CechCohom.restrict X Set.inter_subset_right p).comp (AddMonoidHom.snd _ _)


/-- Mayer–Vietoris connecting homomorphism (normal case)
$\check{H}^p(X, A \cap B) \to \check{H}^{p+1}(X, A \cup B)$ for closed `A`, `B`
in a normal space. -/
noncomputable def mvConnecting
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (p : ℕ) :
    CechCohom X (A ∩ B) p →+ CechCohom X (A ∪ B) (p + 1) := by sorry


/-- Exactness at $\check{H}^p(X, A \cup B)$: $\mathrm{im}(\delta) = \ker(\mathrm{restrict})$. -/
theorem mvExact_connecting_restrict
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (p : ℕ) :
    Exact (mvConnecting X hA hB p) (mvRestrict X A B (p + 1)) := by sorry

/-- Exactness at $\check{H}^p(X, A) \oplus \check{H}^p(X, B)$:
$\mathrm{im}(\mathrm{restrict}) = \ker(\mathrm{diff})$. -/
theorem mvExact_restrict_diff
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (p : ℕ) :
    Exact (mvRestrict X A B p) (mvDiff X A B p) := by sorry

/-- Exactness at $\check{H}^p(X, A \cap B)$:
$\mathrm{im}(\mathrm{diff}) = \ker(\delta)$. -/
theorem mvExact_diff_connecting
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (p : ℕ) :
    Exact (mvDiff X A B p) (mvConnecting X hA hB p) := by sorry


/-- Compact analogue of `mvConnecting` for compact `A`, `B` in a Hausdorff
space. -/
noncomputable def mvConnecting_compact
    (X : Type) [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) (p : ℕ) :
    CechCohom X (A ∩ B) p →+ CechCohom X (A ∪ B) (p + 1) := by sorry

/-- Compact analogue of `mvExact_connecting_restrict`. -/
theorem mvExact_connecting_restrict_compact
    (X : Type) [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) (p : ℕ) :
    Exact (mvConnecting_compact X hA hB p) (mvRestrict X A B (p + 1)) := by sorry

/-- Compact analogue of `mvExact_restrict_diff`. -/
theorem mvExact_restrict_diff_compact
    (X : Type) [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) (p : ℕ) :
    Exact (mvRestrict X A B p) (mvDiff X A B p) := by sorry

/-- Compact analogue of `mvExact_diff_connecting`. -/
theorem mvExact_diff_connecting_compact
    (X : Type) [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) (p : ℕ) :
    Exact (mvDiff X A B p) (mvConnecting_compact X hA hB p) := by sorry

/-- **Corollary 35.9 (Mayer–Vietoris).** For closed subsets `A`, `B` of a
normal space `X`, the sequence
$\cdots \to \check{H}^p(X, A \cup B) \to \check{H}^p(X, A) \oplus \check{H}^p(X, B)
\to \check{H}^p(X, A \cap B) \to \check{H}^{p+1}(X, A \cup B) \to \cdots$
is exact. -/
theorem mayerVietoris
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (p : ℕ) :
    Exact (mvConnecting X hA hB p) (mvRestrict X A B (p + 1)) ∧
    Exact (mvRestrict X A B p) (mvDiff X A B p) ∧
    Exact (mvDiff X A B p) (mvConnecting X hA hB p) :=
  ⟨mvExact_connecting_restrict X hA hB p,
   mvExact_restrict_diff X hA hB p,
   mvExact_diff_connecting X hA hB p⟩

end CechCohomology

namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

/-- A **relative neighborhood pair** for `L ⊆ K ⊆ X`: a pair of open sets
`U ⊇ K`, `V ⊇ L` with `V ≤ U`. The directed system indexed by these pairs is
used to define relative Čech cohomology. -/
structure RelNbhdPair {X : Type} [TopologicalSpace X] (K L : Set X) where
  U : Opens X
  V : Opens X
  hK : K ⊆ ↑U
  hL : L ⊆ ↑V
  hVU : V ≤ U

variable {X : Type} [TopologicalSpace X]

/-- Preorder on relative neighborhood pairs: `p ≤ q` iff `q.U ⊆ p.U` and
`q.V ⊆ p.V` (smaller neighborhoods correspond to larger elements). -/
instance relNbhdPair_preorder {K L : Set X} : Preorder (RelNbhdPair K L) where
  le p q := q.U ≤ p.U ∧ q.V ≤ p.V
  le_refl _ := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ hpq hqr := ⟨le_trans hqr.1 hpq.1, le_trans hqr.2 hpq.2⟩

/-- The preorder of relative neighborhood pairs is directed: any two pairs
admit a common refinement obtained by intersecting their components. -/
instance relNbhdPair_directed {K L : Set X} :
    IsDirected (RelNbhdPair K L) (· ≤ ·) where
  directed p q := ⟨⟨p.U ⊓ q.U, p.V ⊓ q.V,
    fun _ hx => ⟨p.hK hx, q.hK hx⟩,
    fun _ hx => ⟨p.hL hx, q.hL hx⟩,
    inf_le_inf p.hVU q.hVU⟩,
    ⟨inf_le_left, inf_le_left⟩, ⟨inf_le_right, inf_le_right⟩⟩

/-- The preorder of relative neighborhood pairs is nonempty: the pair
`(⊤, ⊤)` (the whole space, the whole space) is always a valid neighborhood
pair. -/
instance relNbhdPair_nonempty {K L : Set X} : Nonempty (RelNbhdPair K L) :=
  ⟨⟨⊤, ⊤, fun _ _ => trivial, fun _ _ => trivial, le_refl _⟩⟩

/-- Continuous inclusion $V \hookrightarrow U$ associated to a relative
neighborhood pair `(U, V)`, viewed as a morphism in `TopCat`. -/
def relNbhdInclusion {K L : Set X} (pair : RelNbhdPair K L) :
    TopCat.of ↑pair.V.1 ⟶ TopCat.of ↑pair.U.1 :=
  ⟨fun x => ⟨x.1, pair.hVU x.2⟩, continuous_inclusion pair.hVU⟩

/-- Relative singular cohomology $H^p(U, V; \mathbb{Z})$ of the pair of open
sets `(U, V)` associated to a relative neighborhood pair. -/
noncomputable def relSingCohomOfPair {K L : Set X}
    (pair : RelNbhdPair K L) (p : ℕ) : ModuleCat.{0} ℤ :=
  relativeSingularCohomology ℤ (TopCat.of ↑pair.U.1) (TopCat.of ↑pair.V.1)
    (relNbhdInclusion pair) (ModuleCat.of ℤ ℤ) p

/-- Index-wise family $\mathrm{pair} \mapsto H^p(U_{\mathrm{pair}}, V_{\mathrm{pair}})$
whose direct limit will define relative Čech cohomology. -/
def relCechFam (K L : Set X) (p : ℕ) (pair : RelNbhdPair K L) : Type :=
  (relSingCohomOfPair pair p : Type _)

/-- The additive group structure on each fibre of `relCechFam`. -/
noncomputable instance relCechFam_addCommGroup {K L : Set X}
    (p : ℕ) (pair : RelNbhdPair K L) :
    AddCommGroup (relCechFam K L p pair) :=
  (relSingCohomOfPair pair p).isAddCommGroup

/-- Continuous inclusion `U₂ ↪ U₁` of opens (with `U₂ ≤ U₁`) viewed as a
morphism in `TopCat`. -/
def opensInclusion {U₁ U₂ : Opens X} (h : U₂ ≤ U₁) :
    TopCat.of ↑U₂.1 ⟶ TopCat.of ↑U₁.1 :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- Naturality square for opens inclusions: the two ways of composing the
inclusions $V_2 \hookrightarrow V_1 \hookrightarrow U_1$ and
$V_2 \hookrightarrow U_2 \hookrightarrow U_1$ agree. -/
theorem opensInclusion_comm {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    opensInclusion h.2 ≫ relNbhdInclusion pair₁ =
    relNbhdInclusion pair₂ ≫ opensInclusion h.1 := by
  apply TopCat.ext
  intro x
  rfl

/-- The cochain-restriction operation is contravariantly functorial in
composition of continuous maps. -/
theorem restrictionCochainMap_comp (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrictionCochainMap R G (f ≫ g) =
    restrictionCochainMap R G g ≫ restrictionCochainMap R G f := by
  simp only [restrictionCochainMap, Functor.map_comp]
  rfl

/-- Commutativity of restriction cochain maps along the square of inclusions
associated to `pair₁ ≤ pair₂`: derives from `opensInclusion_comm` and the
contravariant functoriality of restriction. -/
theorem restrictionCochainMap_square {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2) =
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) := by
  rw [← restrictionCochainMap_comp, ← restrictionCochainMap_comp,
      opensInclusion_comm pair₁ pair₂ h]

open CategoryTheory.Limits in
/-- Transition map of relative singular cochain complexes induced by
`pair₁ ≤ pair₂`: the canonical map between kernels of the restriction cochain
maps coming from the commuting square. -/
noncomputable def relCochainComplexMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ⟶
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) :=
  kernel.map
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2))
    (restrictionCochainMap_square pair₁ pair₂ h)

/-- Transition map between relative singular cohomology groups
$H^p(U_1, V_1) \to H^p(U_2, V_2)$ for `pair₁ ≤ pair₂`, obtained by taking
$p$-th homology of `relCochainComplexMap`. -/
noncomputable def relCohomTransitionModMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) (p : ℕ) :
    relSingCohomOfPair pair₁ p ⟶ relSingCohomOfPair pair₂ p :=
  HomologicalComplex.homologyMap (relCochainComplexMap pair₁ pair₂ h) p

/-- Bonding map of the directed system `relCechFam K L p`: the underlying
additive group hom of `relCohomTransitionModMap`. -/
noncomputable def relCechTransitionMap
    {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relCechFam K L p pair₁ →+ relCechFam K L p pair₂ :=
  (relCohomTransitionModMap pair₁ pair₂ h p).hom.toAddMonoidHom

end CechCohomology


open CategoryTheory CategoryTheory.Limits SingularCohomology in
/-- `relCechFam K L p` together with `relCechTransitionMap` is a directed
system: identities act as identities, and composition of bondings respects
composition of inclusions. -/
noncomputable instance CechCohomology.relCechFam_directedSystem_axioms
    {X : Type} [TopologicalSpace X] {K L : Set X} (p : ℕ) :
    DirectedSystem (CechCohomology.relCechFam K L p)
      (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h) where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap (CechCohomology.relCochainComplexMap i i (le_refl i)) p).hom.toAddMonoidHom x = x
    have hid1 : CechCohomology.opensInclusion (le_refl i).1 =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres1 : restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    have hrelMap : CechCohomology.relCochainComplexMap i i (le_refl i) = 𝟙 _ := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))]
      simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
      rw [hid1]
      simp only [hres1, Category.comp_id]
    rw [hrelMap, HomologicalComplex.homologyMap_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    simp only [CechCohomology.relCechTransitionMap, CechCohomology.relCohomTransitionModMap]
    have hcomp1 : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (hij.trans hjk).1 := by
      apply TopCat.ext; intro x; rfl
    have hrelComp : CechCohomology.relCochainComplexMap i j hij ≫
        CechCohomology.relCochainComplexMap j k hjk =
        CechCohomology.relCochainComplexMap i k (hij.trans hjk) := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion k)))]
      simp only [Category.assoc, kernel.lift_ι]
      rw [kernel.lift_ι_assoc]
      simp only [Category.assoc, kernel.lift_ι]
      congr 1
      rw [← CechCohomology.restrictionCochainMap_comp, hcomp1]
    rw [show CechCohomology.relCochainComplexMap i k (hij.trans hjk) =
      CechCohomology.relCochainComplexMap i j hij ≫
      CechCohomology.relCochainComplexMap j k hjk from hrelComp.symm]
    rw [HomologicalComplex.homologyMap_comp]
    rfl

namespace CechCohomology

variable {X : Type} [TopologicalSpace X]

/-- Convenience instance form of `relCechFam_directedSystem_axioms`. -/
instance relCechFam_directedSystem {K L : Set X} (p : ℕ) :
    DirectedSystem (relCechFam K L p)
      (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h) :=
  relCechFam_directedSystem_axioms p

/-- **Relative Čech cohomology** $\check{H}^p(X, K, L)$: the direct limit over
relative neighborhood pairs of `(K, L)` of the relative singular cohomology
$H^p(U, V; \mathbb{Z})$. -/
noncomputable def CechCohomRel
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) : Type :=
  open Classical in
  AddCommGroup.DirectLimit (relCechFam K L p)
    (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)

namespace CechCohomRel

/-- Additive group structure on `CechCohomRel X K L p` from the direct limit. -/
noncomputable instance addCommGroup
    (X : Type) [TopologicalSpace X]
    (K L : Set X) (p : ℕ) : AddCommGroup (CechCohomRel X K L p) :=
  open Classical in
  AddCommGroup.DirectLimit.addCommGroup _ _

end CechCohomRel
end CechCohomology

/-- Restriction of a relative neighborhood pair along inclusions `L₁ ⊆ K₁`,
`L₂ ⊆ K₂`: a neighborhood pair of `(K₁, K₂)` is also one of `(L₁, L₂)`. -/
def CechCohomology.RelNbhdPair.restrict
    {X : Type} [TopologicalSpace X]
    {K₁ K₂ L₁ L₂ : Set X} (h₁ : L₁ ⊆ K₁) (h₂ : L₂ ⊆ K₂)
    (pair : CechCohomology.RelNbhdPair K₁ K₂) :
    CechCohomology.RelNbhdPair L₁ L₂ where
  U := pair.U
  V := pair.V
  hK := h₁.trans pair.hK
  hL := h₂.trans pair.hL
  hVU := pair.hVU


/-- Inclusion-induced homomorphism on relative Čech cohomology
$\check{H}^p(X, K_1, K_2) \to \check{H}^p(X, L_1, L_2)$ for $L_1 \subseteq K_1$,
$L_2 \subseteq K_2$, defined by restricting each neighborhood pair via
`RelNbhdPair.restrict`. -/
noncomputable def CechCohomology.CechCohomRel.inclusionMap
    (X : Type) [TopologicalSpace X]
    {K₁ K₂ L₁ L₂ : Set X} (h₁ : L₁ ⊆ K₁) (h₂ : L₂ ⊆ K₂) (p : ℕ) :
    CechCohomology.CechCohomRel X K₁ K₂ p →+
      CechCohomology.CechCohomRel X L₁ L₂ p :=
  open Classical CechCohomology in
  AddCommGroup.DirectLimit.lift
    (relCechFam K₁ K₂ p)
    (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
    (CechCohomRel X L₁ L₂ p)
    (fun pair => AddCommGroup.DirectLimit.of
      (relCechFam L₁ L₂ p)
      (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
      (pair.restrict h₁ h₂))
    (fun i j hij x => by
      classical
      have hij' : i.restrict h₁ h₂ ≤ j.restrict h₁ h₂ := hij
      exact AddCommGroup.DirectLimit.of_f (G := relCechFam L₁ L₂ p)
        (f := fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
        hij' x)


/-- Surjectivity input to excision: every class in $H^p(U_2, V_2)$ comes from
$H^p(U_1, V_1)$ when `pair₁ ≤ pair₂`. -/
theorem CechCohomology.singularCohomExcisionSurj
    {X : Type} [TopologicalSpace X] {K L : Set X}
    (pair₁ pair₂ : CechCohomology.RelNbhdPair K L)
    (h : pair₁ ≤ pair₂) (p : ℕ)
    (x : CechCohomology.relCechFam K L p pair₂) :
    ∃ (y : CechCohomology.relCechFam K L p pair₁),
      CechCohomology.relCechTransitionMap p pair₁ pair₂ h y = x := by sorry


open Classical in
/-- Surjectivity step in excision: under the cofinality hypothesis separating
`A` and `B`, every class on a neighborhood of `(B, A ∩ B)` lifts through the
inclusion-induced map from neighborhoods of `(A ∪ B, A)`. -/
theorem CechCohomology.excisionSurjectivityHelper
    {X : Type} [TopologicalSpace X] {A B : Set X}
    (hcof₂ : ∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ⊆ U ∧ W ∩ Y ⊆ V)
    (p : ℕ) (q : CechCohomology.RelNbhdPair B (A ∩ B))
    (x : CechCohomology.relCechFam B (A ∩ B) p q) :
    ∃ (pair : CechCohomology.RelNbhdPair (A ∪ B) A)
      (y : CechCohomology.relCechFam (A ∪ B) A p pair),
    CechCohomology.CechCohomRel.inclusionMap X
      (Set.subset_union_right (s := A)) (Set.inter_subset_left (t := B)) p
      (AddCommGroup.DirectLimit.of
        (CechCohomology.relCechFam (A ∪ B) A p)
        (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
        pair y) =
    AddCommGroup.DirectLimit.of
      (CechCohomology.relCechFam B (A ∩ B) p)
      (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h) q x := by

  obtain ⟨W, Y, hWopen, hYopen, hAW, hBY, _, hWYV⟩ :=
    hcof₂ Set.univ q.V.1 isOpen_univ q.V.2 (Set.subset_univ A) q.hL

  have hWY_open : IsOpen (W ∪ Y) := hWopen.union hYopen
  set pair : CechCohomology.RelNbhdPair (A ∪ B) A :=
    ⟨⟨W ∪ Y, hWY_open⟩, ⟨W, hWopen⟩,
      fun z hz => hz.elim (fun ha => Or.inl (hAW ha)) (fun hb => Or.inr (hBY hb)),
      hAW, Set.subset_union_left⟩

  set pairR : CechCohomology.RelNbhdPair B (A ∩ B) :=
    pair.restrict Set.subset_union_right Set.inter_subset_left


  set r : CechCohomology.RelNbhdPair B (A ∩ B) :=
    ⟨⟨(W ∪ Y) ∩ q.U.1, hWY_open.inter q.U.2⟩, ⟨W ∩ q.V.1, hWopen.inter q.V.2⟩,
      fun z hz => ⟨Or.inr (hBY hz), q.hK hz⟩,
      fun z ⟨ha, hb⟩ => ⟨hAW ha, q.hL ⟨ha, hb⟩⟩,
      fun z ⟨hw, hv⟩ => ⟨Or.inl hw, q.hVU hv⟩⟩
  have hPairR_le_r : pairR ≤ r := ⟨Set.inter_subset_left, Set.inter_subset_left⟩
  have hq_le_r : q ≤ r := ⟨Set.inter_subset_right, Set.inter_subset_right⟩

  obtain ⟨y₀, hy₀⟩ := CechCohomology.singularCohomExcisionSurj pairR r hPairR_le_r p
    (CechCohomology.relCechTransitionMap p q r hq_le_r x)


  refine ⟨pair, y₀, ?_⟩


  have hlift : CechCohomology.CechCohomRel.inclusionMap X
      (Set.subset_union_right (s := A)) (Set.inter_subset_left (t := B)) p
      (AddCommGroup.DirectLimit.of
        (CechCohomology.relCechFam (A ∪ B) A p)
        (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
        pair y₀) =
      AddCommGroup.DirectLimit.of
        (CechCohomology.relCechFam B (A ∩ B) p)
        (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
        pairR y₀ := by
    exact AddCommGroup.DirectLimit.lift_of
      (G := CechCohomology.relCechFam (A ∪ B) A p)
      (f := fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
      _ _ _ pair y₀
  rw [hlift]
  rw [← AddCommGroup.DirectLimit.of_f (G := CechCohomology.relCechFam B (A ∩ B) p)
    (f := fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
    hPairR_le_r y₀]
  rw [hy₀]
  exact (AddCommGroup.DirectLimit.of_f (G := CechCohomology.relCechFam B (A ∩ B) p)
    (f := fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
    hq_le_r x)


/-- Injectivity input to excision: in the excisive configuration
$U_1 = W \cup Y$, $V_1 = W$, $U_2 = Y$, $V_2 = W \cap Y$, a relative cohomology
class that vanishes under restriction was already zero. -/
theorem CechCohomology.singularCohomExcisionInjective
    {X : Type} [TopologicalSpace X]
    {K L : Set X}
    (pair₁ pair₂ : CechCohomology.RelNbhdPair K L)
    (h : pair₁ ≤ pair₂)
    (hExc : ∃ (W Y : Set X), IsOpen W ∧ IsOpen Y ∧
      (↑pair₁.U : Set X) = W ∪ Y ∧ (↑pair₁.V : Set X) = W ∧
      (↑pair₂.U : Set X) = Y ∧ (↑pair₂.V : Set X) = W ∩ Y)
    (p : ℕ)
    (x : CechCohomology.relCechFam K L p pair₁)
    (hx : CechCohomology.relCechTransitionMap p pair₁ pair₂ h x = 0) :
    x = 0 := by sorry


open Classical in
/-- Injectivity step in excision: given both cofinality hypotheses, a class on
a neighborhood pair of `(A ∪ B, A)` mapping to zero in the limit over
neighborhood pairs of `(B, A ∩ B)` was already zero in the source limit. -/
theorem CechCohomology.excisionInjectivityHelper
    {X : Type} [TopologicalSpace X] {A B : Set X}
    (hcof₁ : ∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ∪ Y ⊆ U ∧ Y ⊆ V)
    (hcof₂ : ∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ⊆ U ∧ W ∩ Y ⊆ V)
    (p : ℕ) (pair : CechCohomology.RelNbhdPair (A ∪ B) A)
    (x : CechCohomology.relCechFam (A ∪ B) A p pair)
    (hx : CechCohomology.CechCohomRel.inclusionMap X
      (Set.subset_union_right (s := A)) (Set.inter_subset_left (t := B)) p
      (AddCommGroup.DirectLimit.of
        (CechCohomology.relCechFam (A ∪ B) A p)
        (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
        pair x) = 0) :
    AddCommGroup.DirectLimit.of
      (CechCohomology.relCechFam (A ∪ B) A p)
      (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h)
      pair x = 0 := by
  open CechCohomology in

  have hx' : (AddCommGroup.DirectLimit.of (relCechFam B (A ∩ B) p)
      (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
      (pair.restrict Set.subset_union_right Set.inter_subset_left)) x = 0 := by
    have key : (CechCohomRel.inclusionMap X (Set.subset_union_right (s := A))
        (Set.inter_subset_left (t := B)) p)
        ((AddCommGroup.DirectLimit.of (relCechFam (A ∪ B) A p)
          (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h) pair) x) =
        (AddCommGroup.DirectLimit.of (relCechFam B (A ∩ B) p)
          (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
          (pair.restrict Set.subset_union_right Set.inter_subset_left)) x := by
      exact AddCommGroup.DirectLimit.lift_of _ _ _ pair x
    rw [← key]; exact hx

  obtain ⟨q, hq, hzero⟩ := AddCommGroup.DirectLimit.of.zero_exact
    (G := relCechFam B (A ∩ B) p)
    (f := fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
    (pair.restrict Set.subset_union_right Set.inter_subset_left) x hx'

  obtain ⟨W₁, Y₁, hW₁o, hY₁o, hAW₁, hBY₁, hWY₁U, hY₁V⟩ :=
    hcof₁ ↑pair.U ↑q.U pair.U.2 q.U.2 pair.hK q.hK (hq.1)

  obtain ⟨W₂, Y₂, hW₂o, hY₂o, hAW₂, hBY₂, hW₂V, hWY₂V⟩ :=
    hcof₂ ↑pair.V ↑q.V pair.V.2 q.V.2 pair.hL q.hL

  set W := W₁ ∩ W₂ with hW_def
  set Y := Y₁ ∩ Y₂ with hY_def
  have hWo : IsOpen W := hW₁o.inter hW₂o
  have hYo : IsOpen Y := hY₁o.inter hY₂o
  have hAW : A ⊆ W := Set.subset_inter hAW₁ hAW₂
  have hBY : B ⊆ Y := Set.subset_inter hBY₁ hBY₂
  have hWYU : W ∪ Y ⊆ ↑pair.U := by
    intro z hz; rcases hz with h | h
    · exact hWY₁U (Set.mem_union_left _ h.1)
    · exact hWY₁U (Set.mem_union_right _ h.1)
  have hWV : W ⊆ ↑pair.V := fun z hz => hW₂V hz.2
  have hYqU : Y ⊆ ↑q.U := fun z hz => hY₁V hz.1
  have hWYqV : W ∩ Y ⊆ ↑q.V := fun z ⟨hzW, hzY⟩ => hWY₂V ⟨hzW.2, hzY.2⟩

  let pair' : RelNbhdPair (A ∪ B) A :=
    ⟨⟨W ∪ Y, hWo.union hYo⟩, ⟨W, hWo⟩,
     Set.union_subset_union hAW hBY, hAW, Set.subset_union_left⟩
  have hle : pair ≤ pair' := ⟨hWYU, hWV⟩

  let pair₂ : RelNbhdPair B (A ∩ B) :=
    ⟨⟨Y, hYo⟩, ⟨W ∩ Y, hWo.inter hYo⟩, hBY,
     Set.inter_subset_inter hAW hBY, Set.inter_subset_right⟩

  have hle_pr_p2 : pair'.restrict Set.subset_union_right Set.inter_subset_left ≤ pair₂ :=
    ⟨show pair₂.U ≤ (pair'.restrict Set.subset_union_right Set.inter_subset_left).U from
      Set.subset_union_right,
     show pair₂.V ≤ (pair'.restrict Set.subset_union_right Set.inter_subset_left).V from
      Set.inter_subset_left⟩
  have hle_q_p2 : q ≤ pair₂ := ⟨hYqU, hWYqV⟩
  have hle_pr : (pair.restrict Set.subset_union_right
      (Set.inter_subset_left (s := A) (t := B)) : RelNbhdPair B (A ∩ B)) ≤
      (pair'.restrict Set.subset_union_right
      (Set.inter_subset_left (s := A) (t := B)) : RelNbhdPair B (A ∩ B)) := hle

  have hzero2 : relCechTransitionMap p
      (pair.restrict Set.subset_union_right Set.inter_subset_left)
      pair₂ (hq.trans hle_q_p2) x = 0 := by
    have hcomp := (relCechFam_directedSystem (X := X) (K := B) (L := A ∩ B) p).map_map
      hq hle_q_p2 x
    rw [← hcomp, hzero, map_zero]

  set x' := relCechTransitionMap p
    (pair.restrict Set.subset_union_right Set.inter_subset_left)
    (pair'.restrict Set.subset_union_right Set.inter_subset_left) hle_pr x with hx'_def

  have hfactor := (relCechFam_directedSystem (X := X) (K := B) (L := A ∩ B) p).map_map
    hle_pr hle_pr_p2 x

  have hx'_zero : relCechTransitionMap p
      (pair'.restrict Set.subset_union_right Set.inter_subset_left)
      pair₂ hle_pr_p2 x' = 0 := by
    rw [hfactor]; exact hzero2

  let pair'r := pair'.restrict (Set.subset_union_right (s := A)) (Set.inter_subset_left (s := A) (t := B))
  have hexc : ∃ (W' Y' : Set X), IsOpen W' ∧ IsOpen Y' ∧
      (↑pair'r.U : Set X) = W' ∪ Y' ∧
      (↑pair'r.V : Set X) = W' ∧
      (↑pair₂.U : Set X) = Y' ∧ (↑pair₂.V : Set X) = W' ∩ Y' := by
    exact ⟨W₁ ∩ W₂, Y₁ ∩ Y₂, hWo, hYo, rfl, rfl, rfl, rfl⟩
  have hx'_eq_zero : x' = 0 := singularCohomExcisionInjective
    pair'r pair₂ hle_pr_p2 hexc p x' hx'_zero

  have htrans : relCechTransitionMap p pair pair' hle x = 0 := hx'_eq_zero
  rw [← AddCommGroup.DirectLimit.of_f hle, htrans, map_zero]

/-- Abstract excision: whenever the two cofinality conditions hold, the
inclusion-induced map
$\check{H}^p(X, A \cup B, A) \to \check{H}^p(X, B, A \cap B)$ is bijective. -/
theorem CechCohomology.excisionFromCofinality
    (X : Type) [TopologicalSpace X]
    {A B : Set X}
    (hcof : (∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U →
        ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
          W ∪ Y ⊆ U ∧ Y ⊆ V) ∧
      (∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V →
        ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
          W ⊆ U ∧ W ∩ Y ⊆ V))
    (p : ℕ) :
    Function.Bijective (CechCohomology.CechCohomRel.inclusionMap X
      (Set.subset_union_right (s := A) : B ⊆ A ∪ B)
      (Set.inter_subset_left (t := B) : A ∩ B ⊆ A) p) := by
  classical
  open CechCohomology in
  constructor
  ·
    rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [AddMonoidHom.mem_ker] at ha
    induction a using AddCommGroup.DirectLimit.induction_on with
    | ih pair x =>
      simp only [AddSubgroup.mem_bot]
      exact excisionInjectivityHelper hcof.1 hcof.2 p pair x ha
  ·
    intro a
    induction a using AddCommGroup.DirectLimit.induction_on with
    | ih q x =>
      obtain ⟨pair, y, hy⟩ := excisionSurjectivityHelper hcof.2 p q x
      exact ⟨AddCommGroup.DirectLimit.of
        (relCechFam (A ∪ B) A p)
        (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
        pair y, hy⟩

namespace CechCohomology

/-- Bijectivity form of excision (normal case): for closed `A`, `B` in a
normal Hausdorff space, the inclusion
$(B, A \cap B) \hookrightarrow (A \cup B, A)$ induces a bijection on relative
Čech cohomology. -/
theorem cechCohomologyExcision_bijective
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (p : ℕ) :
    Function.Bijective (CechCohomRel.inclusionMap X
      (Set.subset_union_right (s := A) : B ⊆ A ∪ B)
      (Set.inter_subset_left (t := B) : A ∩ B ⊆ A) p) :=
  excisionFromCofinality X (neighborhood_maps_cofinal_normal hA hB) p

/-- **Theorem 35.3 (Excision).** For closed `A`, `B` in a normal Hausdorff
space, the additive equivalence
$\check{H}^p(X, A \cup B, A) \xrightarrow{\sim} \check{H}^p(X, B, A \cap B)$
induced by inclusion. -/
noncomputable def cechCohomologyExcision
    (X : Type) [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (p : ℕ) :
    CechCohomRel X (A ∪ B) A p ≃+ CechCohomRel X B (A ∩ B) p :=
  AddEquiv.ofBijective
    (CechCohomRel.inclusionMap X
      (Set.subset_union_right (s := A) : B ⊆ A ∪ B)
      (Set.inter_subset_left (t := B) : A ∩ B ⊆ A) p)
    (cechCohomologyExcision_bijective X hA hB p)

end CechCohomology


/-- Bijectivity form of excision (compact case): for compact `A`, `B` in a
Hausdorff space, the inclusion-induced map on relative Čech cohomology is
bijective. -/
theorem CechCohomology.cechCohomologyExcision_compact_bijective
    (X : Type) [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) (p : ℕ) :
    Function.Bijective (CechCohomology.CechCohomRel.inclusionMap X
      (Set.subset_union_right (s := A) : B ⊆ A ∪ B)
      (Set.inter_subset_left (t := B) : A ∩ B ⊆ A) p) :=
  CechCohomology.excisionFromCofinality X
    (CechCohomology.neighborhood_maps_cofinal_compact hA hB) p


/-- Map $\check{H}^p(X, K, L) \to \check{H}^p(X, K)$ from relative to absolute
Čech cohomology of a pair (first arrow of the long exact sequence). -/
noncomputable def CechCohomology.relToAbs
    (X : Type) [TopologicalSpace X]
    {K L : Set X} (hLK : L ⊆ K) (p : ℕ) :
    CechCohomology.CechCohomRel X K L p →+ CechCohomology.CechCohom X K p := by sorry

/-- Restriction $\check{H}^p(X, K) \to \check{H}^p(X, L)$ for $L \subseteq K$
(second arrow of the long exact sequence). -/
noncomputable def CechCohomology.lesRestrict
    (X : Type) [TopologicalSpace X]
    {K L : Set X} (hLK : L ⊆ K) (p : ℕ) :
    CechCohomology.CechCohom X K p →+ CechCohomology.CechCohom X L p := by sorry

/-- Connecting homomorphism $\check{H}^p(X, L) \to \check{H}^{p+1}(X, K, L)$
in the long exact sequence of the pair $(K, L)$. -/
noncomputable def CechCohomology.connecting
    (X : Type) [TopologicalSpace X]
    {K L : Set X} (hLK : L ⊆ K) (p : ℕ) :
    CechCohomology.CechCohom X L p →+ CechCohomology.CechCohomRel X K L (p + 1) := by sorry


/-- Index type for the long-exact-sequence directed systems: a synonym for
`RelNbhdPair K L`. -/
def CechCohomology.lesIndexType
    (X : Type) [TopologicalSpace X] (K L : Set X) : Type :=
  CechCohomology.RelNbhdPair K L

/-- Preorder on the LES index type, inherited from `relNbhdPair_preorder`. -/
instance CechCohomology.lesIndexPreorder
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Preorder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_preorder

/-- Directedness of the LES index type. -/
instance CechCohomology.lesIndexDirected
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    IsDirectedOrder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_directed

/-- Classical decidable equality on the LES index type. -/
noncomputable instance CechCohomology.lesIndexDecEq
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    DecidableEq (CechCohomology.lesIndexType X K L) :=
  open Classical in inferInstance

/-- Nonemptiness of the LES index type. -/
instance CechCohomology.lesIndexNonempty
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Nonempty (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_nonempty

/-- Relative cohomology family $i \mapsto H^p(U_i, V_i)$ for the pointwise
long exact sequence. -/
def CechCohomology.relFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  CechCohomology.relCechFam K L p

/-- Additive group structure on each fibre of `relFamily`. -/
noncomputable instance CechCohomology.relFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.relFamily X K L p i) :=
  CechCohomology.relCechFam_addCommGroup p i

/-- Absolute cohomology family $i \mapsto H^p(U_i)$ — middle term of the
pointwise LES. -/
def CechCohomology.absKFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  fun i => (CechCohomology.singCohom (TopCat.of ↑i.U.1) p : Type)

/-- Additive group structure on each fibre of `absKFamily`. -/
noncomputable instance CechCohomology.absKFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.absKFamily X K L p i) :=
  (CechCohomology.singCohom (TopCat.of ↑i.U.1) p).isAddCommGroup

/-- Absolute cohomology family $i \mapsto H^p(V_i)$ — third term of the
pointwise LES. -/
def CechCohomology.absLFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  fun i => (CechCohomology.singCohom (TopCat.of ↑i.V.1) p : Type)

/-- Additive group structure on each fibre of `absLFamily`. -/
noncomputable instance CechCohomology.absLFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.absLFamily X K L p i) :=
  (CechCohomology.singCohom (TopCat.of ↑i.V.1) p).isAddCommGroup

/-- Bonding map for the relative cohomology directed system; re-export of
`relCechTransitionMap`. -/
noncomputable def CechCohomology.relBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.relFamily X K L p i →+ CechCohomology.relFamily X K L p j :=
  CechCohomology.relCechTransitionMap p i j h

/-- `relFamily` together with `relBond` is a directed system. -/
noncomputable instance CechCohomology.relBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.relFamily X K L p)
      fun i j h => CechCohomology.relBond X K L p i j h :=
  CechCohomology.relCechFam_directedSystem_axioms p

/-- Bonding map for `absKFamily`: pullback of singular cohomology along the
open inclusion $U_j \hookrightarrow U_i$. -/
noncomputable def CechCohomology.absKBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.absKFamily X K L p i →+ CechCohomology.absKFamily X K L p j :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom


/-- `absKFamily` together with `absKBond` is a directed system. -/
noncomputable instance CechCohomology.absKBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absKFamily X K L p)
      fun i j h => CechCohomology.absKBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.U))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.U) =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.1)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.1 hij.1))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (le_trans hjk.1 hij.1) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.1 hij.1)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.1) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]

/-- Bonding map for `absLFamily`: pullback of singular cohomology along the
open inclusion $V_j \hookrightarrow V_i$. -/
noncomputable def CechCohomology.absLBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.absLFamily X K L p i →+ CechCohomology.absLFamily X K L p j :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom


/-- `absLFamily` together with `absLBond` is a directed system. -/
noncomputable instance CechCohomology.absLBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absLFamily X K L p)
      fun i j h => CechCohomology.absLBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.V))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.V) =
        𝟙 (TopCat.of ↑i.V.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.V.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.2)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.2 hij.2))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.2 ≫ CechCohomology.opensInclusion hij.2 =
        CechCohomology.opensInclusion (le_trans hjk.2 hij.2) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.2 hij.2)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.2) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]


/-- Pointwise rel-to-abs map at a single neighborhood pair `i = (U, V)`:
$H^p(U, V) \to H^p(U)$, from the kernel inclusion. -/
noncomputable def CechCohomology.ptRelToAbs
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.relFamily X K L p i →+ CechCohomology.absKFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))) p).hom.toAddMonoidHom

/-- Pointwise restriction map at `i = (U, V)`: $H^p(U) \to H^p(V)$, induced by
pullback along the inclusion $V \hookrightarrow U$. -/
noncomputable def CechCohomology.ptRestrict
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.absKFamily X K L p i →+ CechCohomology.absLFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i)) p).hom.toAddMonoidHom


/-- The restriction-of-cochains map associated to a relative neighborhood pair
is an epimorphism in the category of cochain complexes of `ℤ`-modules. -/
theorem CechCohomology.restrictionCochainMap_epi
    {X : Type} [TopologicalSpace X] {K L : Set X}
    (i : CechCohomology.lesIndexType X K L) :
    CategoryTheory.Epi
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) := by sorry

attribute [instance] CechCohomology.restrictionCochainMap_epi

/-- Short exact sequence of cochain complexes
$0 \to C^\bullet(U, V) \to C^\bullet(U) \to C^\bullet(V) \to 0$
for the neighborhood pair `i = (U, V)`. -/
noncomputable def CechCohomology.cochainSES
    {X : Type} [TopologicalSpace X] {K L : Set X}
    (i : CechCohomology.lesIndexType X K L) :
    (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))
      (CategoryTheory.Limits.kernel.condition _)).ShortExact := by
  letI : CategoryTheory.Abelian (CochainComplex (ModuleCat.{0} ℤ) ℕ) := inferInstance
  exact CategoryTheory.ShortComplex.ShortExact.mk
    (CategoryTheory.ShortComplex.exact_of_f_is_kernel _
      (CategoryTheory.Limits.kernelIsKernel _))

/-- Pointwise connecting homomorphism $H^p(V) \to H^{p+1}(U, V)$ associated to
`cochainSES i`. -/
noncomputable def CechCohomology.ptConnecting
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.absLFamily X K L p i →+ CechCohomology.relFamily X K L (p + 1) i :=
  ((CechCohomology.cochainSES i).δ p (p + 1) rfl).hom.toAddMonoidHom


/-- The compatibility square `relCochainComplexMap` followed by the kernel
inclusion equals the kernel inclusion followed by the absolute restriction
cochain map. -/
theorem CechCohomology.relCochainComplexMap_comp_kernel_ι
    {X : Type} [TopologicalSpace X] {K L : Set X}
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.relCochainComplexMap i j h ≫
      CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion j)) =
    CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1) := by
  simp only [CechCohomology.relCochainComplexMap]
  exact CategoryTheory.Limits.kernel.lift_ι _ _ _


/-- Naturality of `ptRelToAbs`: the pointwise rel-to-abs maps commute with the
bonding maps of `relFamily` and `absKFamily`. -/
theorem CechCohomology.ptRelToAbs_nat
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    (CechCohomology.ptRelToAbs X K L p j).comp (CechCohomology.relBond X K L p i j h) =
    (CechCohomology.absKBond X K L p i j h).comp (CechCohomology.ptRelToAbs X K L p i) := by
  ext x
  show (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j))) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i))) p).hom.toAddMonoidHom x)
  have hsq := CechCohomology.relCochainComplexMap_comp_kernel_ι i j h
  have key : HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) p ≫
    HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion j))) p =
    HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i))) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p := by
    rw [show HomologicalComplex.homologyMap
        (CechCohomology.relCochainComplexMap i j h) p ≫
      HomologicalComplex.homologyMap
        (CategoryTheory.Limits.kernel.ι
          (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
            (CechCohomology.relNbhdInclusion j))) p =
      HomologicalComplex.homologyMap
        (CechCohomology.relCochainComplexMap i j h ≫
          CategoryTheory.Limits.kernel.ι
            (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
              (CechCohomology.relNbhdInclusion j))) p
      from (HomologicalComplex.homologyMap_comp _ _ p).symm, hsq]
    exact HomologicalComplex.homologyMap_comp _ _ p
  have h2 := congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h2
  exact h2
/-- Naturality of `ptRestrict`: pointwise restrictions $H^p(U_i) \to H^p(V_i)$
commute with the bonding maps of `absKFamily` and `absLFamily`. -/
theorem CechCohomology.ptRestrict_nat
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    (CechCohomology.ptRestrict X K L p j).comp (CechCohomology.absKBond X K L p i j h) =
    (CechCohomology.absLBond X K L p i j h).comp (CechCohomology.ptRestrict X K L p i) := by
  ext x
  show (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion j)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) p).hom.toAddMonoidHom x)
  have hcomm : CechCohomology.opensInclusion h.2 ≫ CechCohomology.relNbhdInclusion i =
      CechCohomology.relNbhdInclusion j ≫ CechCohomology.opensInclusion h.1 :=
    (CechCohomology.opensInclusion_comm i j h).symm
  have hsq : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion j) =
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.2) := by
    rw [← CechCohomology.restrictionCochainMap_comp,
        ← CechCohomology.restrictionCochainMap_comp, hcomm]
  have key : HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j)) p =
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hsq]
  have h2 := congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h2
  exact h2
/-- Naturality of `ptConnecting`: pointwise connecting homomorphisms commute
with the bondings of `absLFamily` and (shifted) `relFamily`, via
`δ`-naturality of the homology sequence applied to a morphism of short exact
sequences. -/
theorem CechCohomology.ptConnecting_nat
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    (CechCohomology.ptConnecting X K L p j).comp (CechCohomology.absLBond X K L p i j h) =
    (CechCohomology.relBond X K L (p + 1) i j h).comp (CechCohomology.ptConnecting X K L p i) := by

  let φ : (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))
      (CategoryTheory.Limits.kernel.condition _)) ⟶
    (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion j)))
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j))
      (CategoryTheory.Limits.kernel.condition _)) :=
    { τ₁ := CechCohomology.relCochainComplexMap i j h
      τ₂ := SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)
      τ₃ := SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)
      comm₁₂ := CechCohomology.relCochainComplexMap_comp_kernel_ι i j h
      comm₂₃ := (CechCohomology.restrictionCochainMap_square i j h).symm }
  have key := HomologicalComplex.HomologySequence.δ_naturality φ
    (CechCohomology.cochainSES i) (CechCohomology.cochainSES j) p (p + 1) rfl

  ext x
  show ((CechCohomology.cochainSES j).δ p (p + 1) rfl).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) (p + 1)).hom.toAddMonoidHom
    (((CechCohomology.cochainSES i).δ p (p + 1) rfl).hom.toAddMonoidHom x)

  have h2 : (HomologicalComplex.homologyMap φ.τ₃ p ≫
    (CechCohomology.cochainSES j).δ p (p + 1) rfl).hom.toAddMonoidHom x =
    ((CechCohomology.cochainSES i).δ p (p + 1) rfl ≫
    HomologicalComplex.homologyMap φ.τ₁ (p + 1)).hom.toAddMonoidHom x :=
    congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key.symm
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, LinearMap.comp_apply,
    Function.comp_apply, LinearMap.toAddMonoidHom_coe] at h2 ⊢
  exact h2


/-- Pointwise exactness at the absolute term: at each `i`, the sequence
`relFamily → absKFamily → absLFamily` is exact, from
`cochainSES.homology_exact₂`. -/
theorem CechCohomology.ptExact_relToAbs_restrict
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    Function.Exact (CechCohomology.ptRelToAbs X K L p i) (CechCohomology.ptRestrict X K L p i) := by
  have h := (CechCohomology.cochainSES i).homology_exact₂ p
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h
/-- Pointwise exactness at `absLFamily`: at each `i`, the sequence
`absKFamily → absLFamily → relFamily(p+1)` is exact, from
`cochainSES.homology_exact₃`. -/
theorem CechCohomology.ptExact_restrict_connecting
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    Function.Exact (CechCohomology.ptRestrict X K L p i) (CechCohomology.ptConnecting X K L p i) := by
  have h := (CechCohomology.cochainSES i).homology_exact₃ p (p + 1) rfl
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h
/-- Pointwise exactness at `relFamily(p+1)`: at each `i`, the sequence
`absLFamily → relFamily(p+1) → absKFamily(p+1)` is exact, from
`cochainSES.homology_exact₁`. -/
theorem CechCohomology.ptExact_connecting_relToAbs
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    Function.Exact (CechCohomology.ptConnecting X K L p i) (CechCohomology.ptRelToAbs X K L (p + 1) i) := by
  have h := (CechCohomology.cochainSES i).homology_exact₁ p (p + 1) rfl
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h


/-- Definitional identification of `CechCohomRel X K L p` with the direct limit
of `relFamily`. -/
noncomputable def CechCohomology.eqvRel
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.CechCohomRel X K L p ≃+
    AddCommGroup.DirectLimit (CechCohomology.relFamily X K L p)
      (CechCohomology.relBond X K L p) :=
  AddEquiv.refl _


/-- Identification of $\check{H}^p(X, K)$ with the direct limit of `absKFamily`
over relative neighborhood pairs of `(K, L)`: the neighborhoods `U_i` of `K`
appearing as the first component of `RelNbhdPair K L` are cofinal among all
open neighborhoods of `K`. -/
noncomputable def CechCohomology.eqvAbsK
    (X : Type) [TopologicalSpace X] (K L : Set X) (hLK : L ⊆ K) (p : ℕ) :
    CechCohomology.CechCohom X K p ≃+
    AddCommGroup.DirectLimit (CechCohomology.absKFamily X K L p)
      (CechCohomology.absKBond X K L p) := by sorry

/-- Identification of $\check{H}^p(X, L)$ with the direct limit of `absLFamily`
over relative neighborhood pairs of `(K, L)`: the neighborhoods `V_i` of `L`
appearing as the second component are cofinal among all open neighborhoods of
`L`. -/
noncomputable def CechCohomology.eqvAbsL
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.CechCohom X L p ≃+
    AddCommGroup.DirectLimit (CechCohomology.absLFamily X K L p)
      (CechCohomology.absLBond X K L p) := by sorry


/-- Compatibility square: the rel-to-abs map agrees with the direct limit of
pointwise rel-to-abs maps under the equivalences `eqvRel` and `eqvAbsK`. -/
theorem CechCohomology.comm_relToAbs
    (X : Type) [TopologicalSpace X] {K L : Set X} (hLK : L ⊆ K) (p : ℕ) :
    (CechCohomology.relToAbs X hLK p).comp
      (CechCohomology.eqvRel X K L p).symm.toAddMonoidHom =
    (CechCohomology.eqvAbsK X K L hLK p).symm.toAddMonoidHom.comp
      (AddCommGroup.DirectLimit.map (CechCohomology.ptRelToAbs X K L p)
        (CechCohomology.ptRelToAbs_nat X K L p)) := by sorry

/-- Compatibility square: the restriction map agrees with the direct limit of
pointwise restrictions under `eqvAbsK` and `eqvAbsL`. -/
theorem CechCohomology.comm_lesRestrict
    (X : Type) [TopologicalSpace X] {K L : Set X} (hLK : L ⊆ K) (p : ℕ) :
    (CechCohomology.lesRestrict X hLK p).comp
      (CechCohomology.eqvAbsK X K L hLK p).symm.toAddMonoidHom =
    (CechCohomology.eqvAbsL X K L p).symm.toAddMonoidHom.comp
      (AddCommGroup.DirectLimit.map (CechCohomology.ptRestrict X K L p)
        (CechCohomology.ptRestrict_nat X K L p)) := by sorry

/-- Compatibility square: the connecting map agrees with the direct limit of
pointwise connecting maps under `eqvAbsL` and `eqvRel` (shifted by one). -/
theorem CechCohomology.comm_connecting
    (X : Type) [TopologicalSpace X] {K L : Set X} (hLK : L ⊆ K) (p : ℕ) :
    (CechCohomology.connecting X hLK p).comp
      (CechCohomology.eqvAbsL X K L p).symm.toAddMonoidHom =
    (CechCohomology.eqvRel X K L (p + 1)).symm.toAddMonoidHom.comp
      (AddCommGroup.DirectLimit.map (CechCohomology.ptConnecting X K L p)
        (CechCohomology.ptConnecting_nat X K L p)) := by sorry

namespace CechCohomology

open Function


/-- **Theorem 35.2 (Long exact sequence of a pair in Čech cohomology).** For
closed $L \subseteq K \subseteq X$, the sequence
$\cdots \to \check{H}^p(X, K, L) \to \check{H}^p(X, K) \to \check{H}^p(X, L)
\to \check{H}^{p+1}(X, K, L) \to \cdots$
is exact. Proved by combining the pointwise short-exact sequences of
neighborhood pairs with `addCommGroup_directLimit_map_exact` and transporting
along the equivalences `eqvRel`, `eqvAbsK`, `eqvAbsL`. -/
theorem longExactSequence
    (X : Type) [TopologicalSpace X]
    {K L : Set X} (_hK : IsClosed K) (_hL : IsClosed L) (hLK : L ⊆ K) (p : ℕ) :
    Exact (relToAbs X hLK p) (lesRestrict X hLK p) ∧
    Exact (lesRestrict X hLK p) (connecting X hLK p) ∧
    Exact (connecting X hLK p) (relToAbs X hLK (p + 1)) :=
  have dlExact1 := addCommGroup_directLimit_map_exact
    (ptRelToAbs X K L p) (ptRelToAbs_nat X K L p)
    (ptRestrict X K L p) (ptRestrict_nat X K L p)
    (ptExact_relToAbs_restrict X K L p)
  have dlExact2 := addCommGroup_directLimit_map_exact
    (ptRestrict X K L p) (ptRestrict_nat X K L p)
    (ptConnecting X K L p) (ptConnecting_nat X K L p)
    (ptExact_restrict_connecting X K L p)
  have dlExact3 := addCommGroup_directLimit_map_exact
    (ptConnecting X K L p) (ptConnecting_nat X K L p)
    (ptRelToAbs X K L (p + 1)) (ptRelToAbs_nat X K L (p + 1))
    (ptExact_connecting_relToAbs X K L p)
  ⟨(Exact.iff_of_ladder_addEquiv
      (eqvRel X K L p).symm (eqvAbsK X K L hLK p).symm (eqvAbsL X K L p).symm
      (comm_relToAbs X hLK p) (comm_lesRestrict X hLK p)).mpr dlExact1,
   (Exact.iff_of_ladder_addEquiv
      (eqvAbsK X K L hLK p).symm (eqvAbsL X K L p).symm (eqvRel X K L (p + 1)).symm
      (comm_lesRestrict X hLK p) (comm_connecting X hLK p)).mpr dlExact2,
   (Exact.iff_of_ladder_addEquiv
      (eqvAbsL X K L p).symm (eqvRel X K L (p + 1)).symm (eqvAbsK X K L hLK (p + 1)).symm
      (comm_connecting X hLK p) (comm_relToAbs X hLK (p + 1))).mpr dlExact3⟩
